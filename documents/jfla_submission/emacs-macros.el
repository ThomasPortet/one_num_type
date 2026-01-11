(defalias 'mkv
   (kmacro "\\ b e g i n { v e r b a t i m } <return> \\ e n d { v e r b a t i m } <return> C-p"))

(defalias 'mki
   (kmacro "\\ b e g i n { i t e m i z e } <return> \\ i t e m SPC <return> \\ e n d { i t e m i z e } <return> C-p C-p C-e"))

(defalias 'mke
   (kmacro "\\ b e g i n { e n u m e r a t e } <return> \\ i t e m SPC <return> \\ e n d { e n u m e r a t e } <return> C-p C-p C-e"))

(defalias 'mkf
   (kmacro "\\ b e g i n { f r a m e } <return> \\ f r a m e t i t l e { } <return> \\ e n d { f r a m e } <return> C-p C-p C-e C-b"))
