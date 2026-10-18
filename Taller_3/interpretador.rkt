#lang eopl

;; Integrantes:
;; ANA SOFIA CANTILLO BOLAÑOS       ?????????
;; SARA JULISSA HERNANDEZ HERNANDEZ ?????????
;; HECTOR DANIEL CARABALI VALENCIA  202410213

;; Enlace al repositorio:
;; https://github.com/DanielValencia10/FLP.git


(define lexica
'(
  (white-sp (whitespace) skip)
  (comment ("//" (arbno (not #\newline))) skip)
  (identifier ("@" letter (arbno (or letter digit "?"))) symbol)
  (number (digit (arbno digit)) number)
  (number ("-" digit (arbno digit)) number)
  (number (digit (arbno digit) "." digit (arbno digit)) number)
  (number ("-" digit (arbno digit) "." digit (arbno digit)) number)
  (text (letter (arbno (or letter digit "_"))) symbol)
  )
)

(define gramatica
 '(
   (programa (expresion) un-programa)
   (expresion (number) numero-lit)
   (expresion ("\""text"\"") texto-lit)
   (expresion (identifier) var-exp)
   (expresion ("("expresion primitiva-binaria expresion")") primapp-bin-exp)
   (expresion (primitiva-unaria "("expresion ")") primapp-un-exp)
   (primitiva-binaria ("+") primitiva-suma)
   (primitiva-binaria ("~") primitiva-resta)
   (primitiva-binaria ("/") primitiva-div)
   (primitiva-binaria ("*") primitiva-multi)
   (primitiva-binaria ("concat") primitiva-concat)
   (primitiva-binaria (">") primitiva-mayor)
   (primitiva-binaria ("<") primitiva-menor)
   (primitiva-binaria (">=") primitiva-mayor-igual)
   (primitiva-binaria ("<=") primitiva-menor-igual)
   (primitiva-binaria ("!=") primitiva-diferente)
   (primitiva-binaria ("==") primitiva-comparador-igual)
   (primitiva-unaria ("longitud") primitiva-longitud)
   (primitiva-unaria ("add1") primitiva-add1)
   (primitiva-unaria ("sub1") primitiva-sub1)
   (primitiva-unaria ("neg") primitiva-negacion-booleana)
  )
)

(sllgen:make-define-datatypes lexica gramatica)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes lexica gramatica))
)

(define scan&parse
  (sllgen:make-string-parser lexica gramatica)
)

(define just-scan
  (sllgen:make-string-scanner lexica gramatica)
)