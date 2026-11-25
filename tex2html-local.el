;;; tex2html-local.el --- Site HTML postprocessing  -*- lexical-binding: t; -*-

;;; Commentary:

;; Site-specific additions to tex2html.el, loaded by it when present.
;; They run on `tex2html-postprocess-html-functions', after the generic
;; steps have resolved \ref, \eqref and section numbers from the aux files.
;;
;; - Theorem-like environments get their LaTeX numbers (Problem 2.1.3)
;;   instead of pandoc's running count (Problem 3).
;; - `thebibliography' entries get their labels and anchors back, and
;;   \cite renders as [Dav, Ch. 4] linking to them, instead of citeproc's
;;   "(Dav?, Ch. 4)".
;; - Accents on expanded macros (\bar\F) and nested aligned blocks
;;   are repaired for MathJax.
;; - Table-of-contents entries repeat the numbered heading text.

;;; Code:

(require 'cl-lib)
(require 'sgml-mode)
(require 'subr-x)
(require 'xml)

(defvar tex2html-theorem-names)
(declare-function label-number-hash-table "tex2html")
(declare-function tex2html-detex "tex2html")

(defun tex2html-local--div-end (beg)
  "Return the end of the element starting at BEG."
  (save-excursion
    (goto-char beg)
    (sgml-skip-tag-forward 1)
    (point)))

(defun tex2html-local--shared-counters (texfile)
  "Map each environment of TEXFILE declared as \\newtheorem{ENV}[COUNTER]
to COUNTER, in a hash table."
  (let ((map (make-hash-table :test 'equal)))
    (when (file-exists-p texfile)
      (with-temp-buffer
        (insert-file-contents texfile)
        (goto-char (point-min))
        (while (re-search-forward
                "\\\\newtheorem\\*?{\\([^}]+\\)}\\[\\([^]]+\\)\\]" nil t)
          (puthash (match-string 1) (match-string 2) map))))
    map))

(defun tex2html-local-fix-theorem-numbers (auxfile)
  "Number theorem-like divs as LaTeX does, using AUXFILE.
Labelled environments take their number from the aux file.  Unlabelled
ones continue the count of their counter within the current section, as
for \\newtheorem{problem}{Problem}[section].  Environments declared
with \\newtheorem{ENV}[COUNTER] in the note share COUNTER."
  (let ((labels (label-number-hash-table auxfile))
        (shared (tex2html-local--shared-counters
                 (concat (file-name-sans-extension auxfile) ".tex")))
        (counters (make-hash-table :test 'equal))
        (env-re (regexp-opt tex2html-theorem-names))
        prefix)
    (goto-char (point-min))
    (while (re-search-forward
            (concat "<h1\\([^>]*\\)>\\|<div\\(?: id=\"\\([^\"]+\\)\"\\)? class=\"\\("
                    env-re "\\)\">")
            nil t)
      (if (match-beginning 1)
          (let ((attrs (match-string 1)))
            (unless (string-match-p "unnumbered" attrs)
              (clrhash counters)
              (setq prefix
                    (and (string-match "id=\"\\([^\"]+\\)\"" attrs)
                         (gethash (match-string 1 attrs) labels)))))
        (let* ((label (match-string 2))
               (env (gethash (match-string 3) shared (match-string 3)))
               (end (tex2html-local--div-end (match-beginning 0)))
               (number (and label (gethash label labels))))
          (if number
              (when (string-match "\\([0-9]+\\)\\'" number)
                (puthash env (string-to-number (match-string 1 number))
                         counters))
            (let ((n (1+ (gethash env counters 0))))
              (puthash env n counters)
              (setq number (if prefix (format "%s.%d" prefix n)
                             (number-to-string n)))))
          (when (re-search-forward
                 "<strong>\\([^<]*?\\) [0-9.]+</strong>" end t)
            (replace-match (concat "<strong>\\1 " number "</strong>")
                           t nil)))))))

(defun tex2html-local--bibitems (texfile)
  "Return the \\bibitem entries of TEXFILE as (KEY LABEL BODY) lists.
BODY is the TeX source of the entry."
  (when (file-exists-p texfile)
    (with-temp-buffer
      (insert-file-contents texfile)
      (goto-char (point-min))
      (let ((bib-end (save-excursion
                       (and (re-search-forward "\\\\end{thebibliography}" nil t)
                            (match-beginning 0))))
            (item-re "\\\\bibitem\\(?:\\[\\([^]]*\\)\\]\\)?{\\([^}]+\\)}")
            items (n 0))
        (while (and bib-end (re-search-forward item-re bib-end t))
          (setq n (1+ n))
          (let* ((key (string-trim (match-string 2)))
                 (label (or (match-string 1) (number-to-string n)))
                 (body-beg (match-end 0))
                 (body-end (save-excursion
                             (if (re-search-forward item-re bib-end t)
                                 (match-beginning 0)
                               bib-end))))
            (push (list key (tex2html-detex label)
                        (string-trim (buffer-substring-no-properties
                                      body-beg body-end)))
                  items)))
        (nreverse items)))))

(defun tex2html-local--latex-to-html (tex)
  "Convert the LaTeX fragment TEX to HTML with pandoc."
  (with-temp-buffer
    (insert tex)
    (if (eq 0 (call-process-region (point-min) (point-max) "pandoc" t '(t nil) nil
                                   "-f" "latex" "-t" "html" "--wrap=none"
                                   "--mathjax"))
        (string-trim (buffer-string))
      (message "Warning: pandoc failed on bibliography entry: %s" tex)
      (xml-escape-string (tex2html-detex tex)))))

(defun tex2html-local--entry-html (body)
  "Return the HTML of a bibliography entry BODY, without paragraph tags."
  (let ((html (tex2html-local--latex-to-html body)))
    (if (string-match "\\`<p>\\(\\(?:.\\|\n\\)*\\)</p>\\'" html)
        (match-string 1 html)
      html)))

(defun tex2html-local-fix-bibliography (auxfile)
  "Rebuild the bibliography of AUXFILE's note and render its citations.
Pandoc drops \\bibitem labels and merges entries not separated by
blank lines, so the list is rebuilt from the TeX source with anchors
ref-KEY, and citations become [Label, note] links to them."
  (let* ((texfile (concat (file-name-sans-extension auxfile) ".tex"))
         (items (tex2html-local--bibitems texfile)))
    (when items
      (goto-char (point-min))
      (when (re-search-forward "<div class=\"thebibliography\">" nil t)
        (let ((beg (match-beginning 0))
              (end (tex2html-local--div-end (match-beginning 0))))
          (delete-region beg end)
          (goto-char beg)
          (insert "<h1 class=\"unnumbered\" id=\"references\">References</h1>\n"
                  "<div class=\"thebibliography\">\n")
          (dolist (item items)
            (insert (format "<p id=\"ref-%s\"><span class=\"bib-label\">[%s]</span> %s</p>\n"
                            (nth 0 item) (nth 1 item)
                            (tex2html-local--entry-html (nth 2 item)))))
          (insert "</div>")))
      ;; Citations: (<strong>Key?</strong>, note) -> [Label, note].
      (goto-char (point-min))
      (while (re-search-forward "<span[[:space:]]+class=\"citation\"[[:space:]]+data-cites=\"[^\"]*\">" nil t)
        (let* ((beg (match-beginning 0))
               (content-beg (match-end 0))
               (end (copy-marker (tex2html-local--div-end beg)))
               (content-end (- end (length "</span>"))))
          (goto-char content-beg)
          (when (and (eq (char-after content-beg) ?\()
                     (eq (char-before content-end) ?\)))
            (save-excursion
              (goto-char (1- content-end))
              (delete-char 1)
              (insert "]"))
            (delete-char 1)
            (insert "["))
          (while (re-search-forward "<strong>\\([^<]+\\)\\?</strong>" end t)
            (let* ((key (match-string 1))
                   (label (nth 1 (assoc key items))))
              (when label
                (replace-match (format "<a href=\"#ref-%s\">%s</a>" key label)
                               t t))))
          (goto-char end)
          (set-marker end nil))))))

(defun tex2html-local-fix-math (_auxfile)
  "Repair two kinds of math that MathJax rejects.
Pandoc expands macros in place, so \\bar\\F becomes \\bar\\mathbb{F},
in which \\bar takes \\mathbb as its argument; brace such arguments.  The
generic step that turns pandoc's aligned back into align also hits a
genuine aligned nested in another display environment; restore those."
  (goto-char (point-min))
  (while (re-search-forward
          (concat "\\\\\\(bar\\|hat\\|tilde\\|widetilde\\|widehat\\|overline"
                  "\\|underline\\|vec\\|dot\\|ddot\\|check\\|breve\\)"
                  "[ \t]*\\(\\\\\\(?:math[a-z]+\\|operatorname\\|boldsymbol\\)"
                  "{[^{}]*}\\)")
          nil t)
    (replace-match "\\\\\\1{\\2}" t nil))
  (goto-char (point-min))
  (while (re-search-forward "\\\\begin{align}" nil t)
    (unless (save-excursion
              (goto-char (match-beginning 0))
              (skip-chars-backward " \t\n")
              (looking-back "\\\\\\[" (- (point) 2)))
      (replace-match "\\\\begin{aligned}" t nil)
      (when (re-search-forward "\\\\end{align}" nil t)
        (replace-match "\\\\end{aligned}" t nil)))))

(defun tex2html-local-fix-toc (_auxfile)
  "Make table-of-contents entries repeat their headings' text."
  (goto-char (point-min))
  (while (re-search-forward
          "<a href=\"#\\([^\"]+\\)\"[ \n]+id=\"toc-[^\"]*\">\\(\\(?:.\\|\n\\)*?\\)</a>" nil t)
    (let* ((id (match-string 1))
           (text-beg (match-beginning 2))
           (text-end (match-end 2))
           (heading
            (save-excursion
              (goto-char (point-min))
              (when (re-search-forward
                     (format "<h[1-6][^>]* id=\"%s\"[^>]*>\\(\\(?:.\\|\n\\)*?\\)</h[1-6]>"
                             (regexp-quote id))
                     nil t)
                (match-string 1)))))
      (when heading
        (let ((text (string-trim
                     (replace-regexp-in-string
                      "[ \n]+" " "
                      (replace-regexp-in-string "<[^>]*>" "" heading)))))
          (delete-region text-beg text-end)
          (goto-char text-beg)
          (insert text))))))

(defun tex2html-local-fix-multi-cites (_auxfile)
  "Link each citation of several keys to the entry of its first key.
Pandoc links \\cite{A, B} to \"#ref-A B\", which is no anchor."
  (goto-char (point-min))
  (while (re-search-forward "href=\"#ref-\\([^\" ]+\\) [^\"]*\"" nil t)
    (replace-match "href=\"#ref-\\1\"" t)))

(defun tex2html-local-break-table-code (_auxfile)
  "Allow line breaks after dots and underscores in code in table cells.
Long identifiers, such as Lean declaration names, otherwise widen their
column until the table overflows the page."
  (goto-char (point-min))
  (while (re-search-forward "<td[ >]" nil t)
    (let ((end (save-excursion (search-forward "</td>" nil t))))
      (while (and end (re-search-forward "<code>\\([^<]*\\)</code>" end t))
        (let ((text (replace-regexp-in-string
                     "\\([._]\\)" "\\1<wbr>" (match-string 1))))
          (setq end (+ end (- (length text) (length (match-string 1)))))
          (replace-match (concat "<code>" text "</code>") t t))))))

(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-fix-theorem-numbers)
(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-break-table-code t)
(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-fix-multi-cites t)
(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-fix-bibliography t)
(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-fix-math t)
(add-hook 'tex2html-postprocess-html-functions #'tex2html-local-fix-toc t)

(provide 'tex2html-local)
;;; tex2html-local.el ends here
