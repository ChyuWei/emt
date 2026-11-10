;;; emt.el  --- Tokenizing CJK words and symbols with macOS's built-in NLP tokenizer  -*- lexical-binding: t; -*-

;; Copyright (C) 2023 Roife Wu

;; Author: Roife Wu <roifewu@gmail.com>
;; URL: https://github.com/roife/emt
;; Version: 2.1.2
;; Package-Requires: ((emacs "31.1"))
;; Keywords: chinese, cjk, tokenizer, macos, mac, natural language, segmentation

;; This file is NOT a part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; EMT stands for Emacs MacOS Tokenizer.
;; This package use macOS's built-in NLP tokenizer to tokenize and operate on
;; CJK words in Emacs.
;;
;; `emt-mode' installs a handler in `find-word-boundary-function-table' for
;; CJK word characters, so commands based on `forward-word' and
;; `backward-word' use emt's tokenization automatically.

;;; Code:

(eval-when-compile (require 'thingatpt))
(eval-when-compile (require 'subr-x))

;;; Customize

(defgroup emt ()
  "Tokenize CJK words with macOS's built-in NLP tokenizer."
  :group 'chinese
  :prefix "emt-")

(defcustom emt-use-cache t
  "Caches for results of tokenization if non-nil."
  :type 'boolean
  :group 'emt)

(defcustom emt-cache-lru-size 50
  "The size of LRU cache for tokenization results."
  :type 'integer
  :group 'emt)

(defcustom emt-lib-path (concat user-emacs-directory "modules/libEMT" module-file-suffix)
  "The path to the directory of dynamic library for emt."
  :type 'string
  :group 'emt)

;;; Export function

(defconst emt-version "v2.1.2")

(defconst emt--swift-module-lib-name "libEmacsSwiftModuleDynamic")

(defvar emt--root (file-name-directory (or load-file-name buffer-file-name))
  "The path to the root of the package.")

(defun emt--swift-module-lib-path (&optional path)
  "Return the path of the shared Swift module library for PATH."
  (expand-file-name (concat emt--swift-module-lib-name module-file-suffix)
                    (file-name-directory (or path emt-lib-path))))

(defun emt--built-lib-path (lib-name)
  "Return the built release path for LIB-NAME."
  (let ((bin-path (replace-regexp-in-string
                   "\n\\'" ""
                   (shell-command-to-string "swift build -c release --show-bin-path"))))
    (expand-file-name (concat lib-name module-file-suffix) bin-path)))

(defvar emt--cjk-regex-forward (format "\\(\\cc\\|\\cj\\|\\ch\\)+\\W*$")
  "Forward regex for CJK.")

(defvar emt--cjk-regex-backward (format "^\\W*\\(\\cc\\|\\cj\\|\\ch\\)+")
  "Backward regex for CJK.")

(defvar emt--lib-loaded nil
  "Whether dynamic module for emt is loaded.")

(defvar emt--cache-set (make-hash-table :test #'equal)
  "The hash table for caching tokenization results.")

(defvar emt--cache-lru-list nil
  "The LRU list for caching tokenization results.")

(defvar emt--lib-fns
  '(emt--do-split-helper
    emt--word-at-point-or-forward-helper)
  "The list of functions in dynamic module.")

(defun emt--cache-get (key)
  "Get the value of KEY in cache."
  (let ((leading 0))
    (when (zerop (string-match "\\W*" key))
      (setq leading (match-end 0)))
    (setq key (string-trim (substring-no-properties key) "\\W*" "\\W*"))
    (let ((value (gethash key emt--cache-set)))
      (when value
        (setq emt--cache-lru-list (delete key emt--cache-lru-list))
        (push key emt--cache-lru-list))
      (if (zerop leading)
          value
        (mapcar #'(lambda (pair) (cons (+ (car pair) leading)
                                  (+ (cdr pair) leading)))
                value)))))

(defun emt--cache-put (key value)
  "Put KEY and VALUE into cache."
  (let ((leading 0))
    (when (zerop (string-match "\\W*" key))
      (setq leading (match-end 0)))
    (unless (zerop leading)
      (setq value (mapcar #'(lambda (pair) (cons (- (car pair) leading)
                                            (- (cdr pair) leading)))
                          value)))
    (setq key (string-trim (substring-no-properties key) "\\W*" "\\W*"))
    (puthash key value emt--cache-set)
    (setq emt--cache-lru-list (delete key emt--cache-lru-list))
    (push key emt--cache-lru-list)
    (when (> (length emt--cache-lru-list) emt-cache-lru-size)
      (setq emt--cache-lru-list (butlast emt--cache-lru-list)))))

;;; Word boundary integration

(defun emt--cjk-word-char-p (char &optional category-set)
  "Return non-nil if CHAR is a CJK word character.

CATEGORY-SET, when non-nil, is used instead of the category set of CHAR."
  (and (integerp char)
       (with-syntax-table (standard-syntax-table)
         (eq (char-syntax char) ?w))
       (let ((category-set (or category-set (char-category-set char))))
         (and category-set
              (or (aref category-set ?c)
                  (aref category-set ?j)
                  (aref category-set ?h))))))

(defun emt--cjk-run-bounds (pos)
  "Return the bounds of the CJK word run containing POS.

The returned value is a cons cell (BEG . END)."
  (save-excursion
    (let ((inhibit-field-text-motion t))
      (goto-char pos)
      (let ((end (progn (forward-word-strictly 1) (point))))
        (goto-char pos)
        (let ((beg (progn (backward-word-strictly 1) (point))))
          ;; `forward-word-strictly' can include an adjacent non-CJK word
          ;; when POS is exactly at a script boundary.  Trim to CJK chars.
          (save-excursion
            (goto-char beg)
            (when (re-search-forward "\\(\\cc\\|\\cj\\|\\ch\\)" (1+ pos) t)
              (setq beg (match-beginning 0))))
          (save-excursion
            (goto-char end)
            (when (re-search-backward "\\(\\cc\\|\\cj\\|\\ch\\)" beg t)
              (setq end (match-end 0))))
          (cons beg end))))))

(defun emt--token-at (tokens index)
  "Return the token in TOKENS containing INDEX, or nil.

TOKENS can be a list or a vector."
  (let (token)
    (mapc (lambda (bounds)
            (when (and (not token)
                       (<= (car bounds) index)
                       (< index (cdr bounds)))
              (setq token bounds)))
          tokens)
    token))

(defun emt--boundary-fallback (pos limit forward-p)
  "Return a safe one-character boundary for POS, bounded by LIMIT."
  (if forward-p
      (min limit (1+ pos))
    (max limit pos)))

(defun emt--find-word-boundary (pos limit)
  "Find the word boundary at POS, bounded by LIMIT.

This is the handler installed in `find-word-boundary-function-table'."
  (let ((forward-p (< pos limit)))
    (if (not emt--lib-loaded)
        (emt--boundary-fallback pos limit forward-p)
      (let* ((bounds (emt--cjk-run-bounds pos))
             (beg (car bounds))
             (end (cdr bounds)))
        (if (or (>= beg end)
                (not (emt--cjk-word-char-p (char-after pos))))
            (emt--boundary-fallback pos limit forward-p)
          (let* ((text (buffer-substring-no-properties beg end))
                 (index (- pos beg))
                 (tokens (condition-case nil
                             (emt-split text)
                           (error nil)))
                 (token (emt--token-at tokens index)))
            (cond
             ((null token)
              (emt--boundary-fallback pos limit forward-p))
             (forward-p
              (min limit (+ beg (cdr token))))
             (t
              (max limit (+ beg (car token)))))))))))

(defun emt--build-boundary-table ()
  "Build and return a char table for CJK word boundaries."
  (let ((table (make-char-table nil)))
    (map-char-table
     (lambda (range category-set)
       (let ((char (if (consp range) (car range) range)))
         (when (and (integerp char)
                    (emt--cjk-word-char-p char category-set))
           (set-char-table-range table range 'emt--find-word-boundary))))
     (standard-category-table))
    table))

(defvar emt--boundary-table nil
  "Char table used for CJK word boundaries.")

(defvar emt--saved-boundary-table nil
  "Saved default value of `find-word-boundary-function-table'.")

(defvar emt--boundary-table-installed nil
  "Non-nil if `emt--boundary-table' is installed.")

(defun emt--install-boundary-table ()
  "Install `emt--boundary-table' as the default word boundary table."
  (unless emt--boundary-table-installed
    (unless emt--boundary-table
      (setq emt--boundary-table (emt--build-boundary-table)))
    (setq emt--saved-boundary-table
          (default-value 'find-word-boundary-function-table))
    (set-default 'find-word-boundary-function-table emt--boundary-table)
    (setq emt--boundary-table-installed t)))

(defun emt--uninstall-boundary-table ()
  "Restore the default word boundary table."
  (when emt--boundary-table-installed
    (when (eq (default-value 'find-word-boundary-function-table)
              emt--boundary-table)
      (set-default 'find-word-boundary-function-table
                   emt--saved-boundary-table))
    (setq emt--boundary-table-installed nil)
    (setq emt--saved-boundary-table nil)))

(defun emt--get-bounds-at-point (direction)
  "Get the bounds of the CJK string at point.

If DIRECTION is `'forward', return the bounds of the string forward.
If DIRECTION is `'backward', return the bounds of the string backward.
If DIRECTION is `'all', return the bounds of the string forward and backward."
  (let* ((pos (point))
         (beg pos)
         (end pos))
    (when (or (eq direction 'forward) (eq direction 'all))
      (save-excursion
        (forward-word-strictly 1)
        (when (string-match-p emt--cjk-regex-forward
                              (buffer-substring-no-properties pos (point)))
          (setq end (point)))))
    (when (or (eq direction 'backward) (eq direction 'all))
      (save-excursion
        (backward-word-strictly 1)
        (when (string-match-p emt--cjk-regex-backward
                              (buffer-substring-no-properties (point) pos))
          (setq beg (point)))))
    (cons beg end)))

(defun emt--word-at-point (back)
  "Return the word at point.

If BACK is non-nil, return the word backward."
  (unless emt--lib-loaded (error "Dynamic module not loaded"))
  (pcase-let* ((`(,beg . ,end) (emt--get-bounds-at-point 'all))
               (index (- (point) beg))
               (`(,word-beg . ,word-end) (emt--word-at-point-or-forward-helper
                                          (buffer-substring-no-properties beg end)
                                          (if (and back (> index 0)) (1- index) index))))
    (if (eq word-beg word-end)
        (word-at-point)
      (buffer-substring (+ beg word-beg) (+ beg word-end)))))

(defun emt--upperbound (pred vec)
  "Binary search to find the last element in VEC satisfying PRED."
  (if (zerop (length vec)) nil
    (let ((start 0)
          (end (1- (length vec))))
      (while (< start end)
        (let ((mid (ash (+ start end 1) -1)))
          (if (funcall pred (elt vec mid))
              (setq start mid)
            (setq end (1- mid)))))
      (elt vec start))))

(defun emt--lowerbound (pred vec)
  "Binary search to find the first element in VEC satisfying PRED."
  (if (zerop (length vec)) nil
    (let ((start 0)
          (end (1- (length vec))))
      (while (< start end)
        (let ((mid (ash (+ start end) -1)))
          (if (funcall pred (elt vec mid))
              (setq end mid)
            (setq start (1+ start)))))
      (elt vec end))))

(defun emt--move-by-word-decide-bounds-direction (direction)
  "Decide the direction when moving by word.

DIRECTION is the direction of moving by word."
  (if (eq direction 'forward)
      (if (and (char-after) (string-match "\\W" (char-to-string (char-after))))
          'forward
        'all)
    (if (and (char-before) (string-match "\\W" (char-to-string (char-before))))
        'backward
      'all)))

(defun emt--move-by-word (direction)
  "Move point by word.

If DIRECTION is `'forward', move point forward by word.
If DIRECTION is `'backward', move point backward by word."
  (pcase-let ((forward-p (eq direction 'forward))
              (`(,beg . ,end) (emt--get-bounds-at-point
                               (emt--move-by-word-decide-bounds-direction direction))))
    (if (eq beg end)
        (if forward-p (forward-word-strictly 1) (backward-word-strictly 1))
      (let* ((text (buffer-substring-no-properties beg end))
             (pos (- (point) beg))
             (pred (if forward-p (lambda (x) (> x pos)) (lambda (x) (< x pos))))
             (target-bound (funcall (if forward-p #'emt--lowerbound #'emt--upperbound)
                                    pred
                                    (mapcar (if forward-p #'cdr #'car) (emt-split text)))))
        (if (and target-bound (funcall pred target-bound))
            (goto-char (+ beg target-bound))
          (if forward-p (forward-word-strictly 1) (backward-word-strictly 1)))))))

(defun emt-split (str)
  "Split STR into a sequence of words.

Return a sequence of word bounds (a cons of the beginning position and the
ending position of a word)."
  (if emt--lib-loaded
      (if-let* ((cached (and emt-use-cache (emt--cache-get str))))
          cached
        (let ((result (emt--do-split-helper str)))
          (when emt-use-cache (emt--cache-put str result))
          result))
    (error "Dynamic module not loaded")))

(defun emt-get-arch ()
  (cond
   ((string-match-p "aarch64" system-configuration)
    "aarch64")
   ((string-match-p "x86_64" system-configuration)
    "x86_64")
   (t
    (error "Unknow architecture")))
  )

;;;###autoload
(defun emt-word-at-point-or-forward ()
  "Return the word at point.

If current point is at bound of a word, return the one forward."
  (interactive)
  (emt--word-at-point nil))

;;;###autoload
(defun emt-word-at-point-or-backward ()
  "Return the word at point.

If current point is at bound of a word, return the one backward."
  (interactive)
  (emt--word-at-point t))

;;;###autoload
(defun emt-download-module (&optional path)
  "Download dynamic module from GitHub release.

If PATH is non-nil, download the module to PATH."
    (interactive)
    (unless (eq system-type 'darwin)
      (error "EMT only support macOS"))
    (setq path (or path emt-lib-path))
    (make-directory (file-name-directory path) t)
    (let* ((arch (emt-get-arch))
           (url (format "https://github.com/roife/emt/releases/download/%s/libEMT-%s.dylib" emt-version arch))
           (swift-module-path (emt--swift-module-lib-path path))
           (swift-module-url (format "https://github.com/roife/emt/releases/download/%s/%s-%s.dylib"
                                     emt-version emt--swift-module-lib-name arch)))
      (url-copy-file swift-module-url swift-module-path t)
      (url-copy-file url path t)))

;;;###autoload
(defun emt-compile-module (&optional path)
  "Compile dynamic module.

If PATH is non-nil, compile the module to PATH."
  (interactive)
  (unless (eq system-type 'darwin)
    (error "Only support macOS"))
  (unless module-file-suffix
    (error "Variable `module-file-suffix' is nil"))
  (unless (executable-find "swift")
    (error "Swift compiler not found"))
  (unless (file-directory-p (concat emt--root "module/"))
    (error "No module source found"))
  (unless (file-exists-p "/Applications/Xcode.app")
    (error "Xcode not found. You can download pre-compiled module from GitHub"))

  (shell-command (concat "echo " (shell-quote-argument (read-passwd "sudo password (required by compiling EMT):"))
                         " | sudo -S xcode-select --switch /Applications/Xcode.app/Contents/Developer"))

  (setq path (or path emt-lib-path))
  (let ((default-directory (concat emt--root "module/")))
    (if (zerop (shell-command "swift build -c release"))
        (progn (message "Compile succeed!")
               (make-directory (file-name-directory path) t)
               (copy-file (emt--built-lib-path "libEMT") path t)
               (copy-file (emt--built-lib-path emt--swift-module-lib-name)
                          (emt--swift-module-lib-path path)
                          t))
      (error "Compile dynamic module failed"))))

;;;###autoload
(defun emt-forward-word (&optional arg)
  "CJK compatible version of `forward-word'.

Move point forward ARG words (backward if ARG is negative).
If ARG is omitted or nil, move point forward one word."
  (interactive "^p")
  (setq arg (or arg 1))
  (let ((direction (if (< arg 0) 'backward 'forward))
        (count (abs arg))
        (i 0))
    (while (and (< i count) (emt--move-by-word direction))
      (setq i (1+ i)))
    (eq i count)))

;;;###autoload
(defun emt-backward-word (&optional arg)
  "CJK compatible version of `backward-word'.

Move point backward ARG words (forward if ARG is negative).
If ARG is omitted or nil, move point forward one word."
  (interactive "^p")
  (setq arg (or arg 1))
  (emt-forward-word (- arg)))

;;;###autoload
(defun emt-kill-word (arg)
  "CJK compatible version of `kill-word'.

Kill characters forward until encountering the end of a word.
With argument ARG, do this that many times."
  (interactive "p")
  (kill-region (point) (progn (emt-forward-word arg) (point))))

;;;###autoload
(defun emt-backward-kill-word (arg)
  "CJK compatible version of `backward-kill-word'.

Kill characters backward until encountering the beginning of a word.
With argument ARG, do this that many times."
  (interactive "p")
  (emt-kill-word (- arg)))

;;;###autoload
(defun emt-mark-word (&optional arg)
  "CJK compatible version of `mark-word'.

Set mark ARG words from point or move mark one word."
  (interactive "p")
  (set-mark (point))
  (emt-forward-word arg))

;;;###autoload
(defun emt-ensure ()
  "Load the dynamic library."
  (interactive)
  (unless emt--lib-loaded
    (unless (file-exists-p emt-lib-path)
      (if (yes-or-no-p "EMT module not found. Download pre-built from GitHub?")
          (emt-download-module)
        (if (yes-or-no-p "Compile EMT module from source?")
            (emt-compile-module)
          (error "EMT module cannot be loaded"))))
    (load-file emt-lib-path)
    (dolist (fn emt--lib-fns)
      (unless (fboundp fn)
        (error "No %s function found in dynamic module" fn)))
    (setq emt--lib-loaded t)))

;;; Minor mode

;;;###autoload
(defvar emt-mode-map (make-sparse-keymap)
  "Keymap for `emt-mode'.

EMT no longer remaps word commands.  It installs a
`find-word-boundary-function-table' handler instead, so this map is
kept empty for compatibility.")

;;;###autoload
(define-minor-mode emt-mode
  "Minor mode for tokenizing CJK words with macOS's built-in NLP tokenizer.

It installs an emt handler in `find-word-boundary-function-table', so
commands based on `forward-word' and `backward-word' use emt's
tokenization."
  :global t
  :keymap emt-mode-map
  :lighter "emt"
  (if emt-mode
      (progn
        (emt-ensure)
        (emt--install-boundary-table))
    (emt--uninstall-boundary-table)))

(provide 'emt)

;;; emt.el ends here
