;; Save this file in your home directory with the name ".emacs"

;;
;;  Agda Setup
;;

(load-file (let ((coding-system-for-read 'utf-8))
             (shell-command-to-string "agda-mode locate")))

(require 'agda-input)

(add-hook 'agda2-mode-hook
	  (lambda () (progn
		       (local-set-key (kbd "C-c ,") 'agda2-goal-and-context)
		       (local-set-key (kbd "C-c .") 'agda2-goal-and-context-and-inferred))))

(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))

;;
;;  Customizations
;;

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(agda2-highlight-datatype-face ((t (:foreground "color-32"))))
 '(agda2-highlight-function-face ((t (:foreground "color-32"))))
 '(agda2-highlight-keyword-face ((t (:foreground "color-216"))))
 '(agda2-highlight-module-face ((t (:foreground "color-135"))))
 '(agda2-highlight-number-face ((t (:foreground "color-135"))))
 '(agda2-highlight-primitive-face ((t (:foreground "color-32"))))
 '(agda2-highlight-symbol-face ((t (:foreground "brightcyan"))))
 '(font-lock-comment-face ((t (:foreground "brightred"))))
 '(highlight ((t (:background "color-236"))))
 '(minibuffer-prompt ((t (:foreground "brightmagenta"))))
 '(widget-field ((t (:background "color-241" :foreground "black")))))
