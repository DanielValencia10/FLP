#lang eopl

;; Integrantes:
;; ANA SOFIA CANTILLO BOLAÑOS       202610112
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
  (text (letter (arbno (or letter digit "_"))) string)
  )
)

(define gramatica
 '(
   (programa (expresion) un-programa)
   (expresion (number) numero-lit)
   (expresion ("\""text"\"") texto-lit)
   (expresion (identifier) var-exp)
   (expresion ("(" expresion primitiva-binaria expresion ")") primapp-bin-exp)
   (expresion (primitiva-unaria "("expresion ")") primapp-un-exp)
   (expresion ("Si" expresion "{" expresion "}" "sino" "{" expresion "}") condicional-exp )
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

;; ============================================================
;; Construcción de los datatypes y del parser a partir de la
;; especificación léxica y la gramática
;; ============================================================

;; Crea automáticamente los datatypes del árbol de sintaxis
;; (programa, expresion, primitiva-binaria, primitiva-unaria).
(sllgen:make-define-datatypes lexica gramatica)

;; Muestra los datatypes que sllgen generó a partir de la gramática.
;; Se usa para revisar cómo quedó el árbol de sintaxis.
(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes lexica gramatica))
)

;; Recibe un texto, lo escanea y lo parsea, y retorna su árbol de sintaxis.
;; Se usa para probar programas escritos como string.
(define scan&parse
  (sllgen:make-string-parser lexica gramatica)
)

;; Recibe un texto y retorna solo la lista de tokens (sin parsear).
;; Se usa para revisar la especificación léxica.
(define just-scan
  (sllgen:make-string-scanner lexica gramatica)
)

;; ============================================================
;; Ambiente
;; ============================================================

;; Predicado que acepta cualquier valor de Scheme.
;; Se usa para validar la lista de valores guardados en el ambiente.
(define scheme-value? (lambda (v) #t))

;; Datatype del ambiente:
;;  - vacio: ambiente sin variables.
;;  - extendido: lista de símbolos, lista de valores y el ambiente anterior.
(define-datatype ambiente ambiente?
  (vacio)
  (extendido (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env ambiente?)))

;; Recibe un predicado y una lista; retorna la posición del primer
;; elemento que cumple el predicado, o #f si ninguno lo cumple.
;; Se usa como auxiliar para buscar variables en el ambiente.
(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;; Recibe un símbolo y una lista de símbolos; retorna la posición
;; del símbolo en la lista, o #f si no está.
(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

;; Crea un ambiente vacío.
(define empty-env
  (lambda ()
    (vacio)))

;; Recibe una lista de símbolos, una lista de valores y un ambiente;
;; retorna un nuevo ambiente que agrega esas variables al anterior.
(define extend-env
  (lambda (syms vals env)
    (extendido syms vals env)
    )
  )

;; Recibe un ambiente y un símbolo; retorna el valor de la variable.
;; Si no está en el ambiente actual la busca en el anterior, y si
;; llega al ambiente vacío lanza el error de variable inexistente.
(define apply-env
  (lambda (env sym)
    (cases ambiente env
      (vacio ()
                        (eopl:error 'apply-env "Error, la variable no existe ~s" sym))
      (extendido (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))))))

;; Retorna el ambiente inicial con las variables @a @b @c @d @e
;; y los valores 1 2 3 "hola" "FLP".
;; Es el ambiente con el que se evalúa todo programa.
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e)
     '(1 2 3 "hola" "FLP")
     (empty-env)
     )
    )
  )

;; ============================================================
;; Booleanos
;; ============================================================

;; Recibe un booleano de Racket (#t o #f) y lo convierte en 1 o 0.
;; Se usa para que las comparaciones del lenguaje retornen 1 o 0.
(define boolean-out
  (lambda (boolean-exp)
    (if boolean-exp 1 0)))

;; Recibe un valor y retorna #f si es 0 y #t en cualquier otro caso.
;; Define qué es verdadero y qué es falso en el lenguaje.
(define valor-verdad?
  (lambda (exp)
    (not (eqv? exp 0))))

;; ============================================================
;; Primitivas
;; ============================================================

;; Recibe una primitiva binaria y una lista con sus dos argumentos;
;; retorna el resultado de aplicar la operación.
(define apply-primitive-bin
  (lambda (prim args)
    (cases primitiva-binaria prim
      (primitiva-suma () (+ (car args) (cadr args)))
      (primitiva-resta () (- (car args) (cadr args)))
      (primitiva-multi () (* (car args) (cadr args)))
      (primitiva-div () (if (= (cadr args) 0) (eopl:error 'apply-primitive-bin "division by zero") (/ (car args) (cadr args))))
      (primitiva-concat () (string-append (car args) (cadr args)))
      (primitiva-mayor () (boolean-out (> (car args) (cadr args))))
      (primitiva-menor () (boolean-out (< (car args) (cadr args))))
      (primitiva-mayor-igual () (boolean-out (>= (car args) (cadr args))))
      (primitiva-menor-igual () (boolean-out (<= (car args) (cadr args))))
      (primitiva-diferente () (boolean-out (not (equal? (car args) (cadr args)))))
      (primitiva-comparador-igual () (boolean-out (equal? (car args) (cadr args))))
   )))

;; Recibe una primitiva unaria y una lista con su argumento;
;; retorna el resultado de aplicar la operación.
(define apply-primitive-un
  (lambda (prim args)
    (cases primitiva-unaria prim
      (primitiva-add1 () (+ (car args) 1))
      (primitiva-sub1 () (- (car args) 1))
      (primitiva-longitud () (string-length (car args)))
      (primitiva-negacion-booleana () (boolean-out (not (valor-verdad? (car args))))))
    )
  )

;; ============================================================
;; Evaluación
;; ============================================================

;; Recibe una expresión y un ambiente; retorna el valor de la expresión.
;; Es el corazón del interpretador: decide qué hacer según el tipo
;; de expresión (número, texto, variable o primitiva).
(define evaluar-expresion
  (lambda (exp env)
    (cases expresion exp
      (numero-lit (datum) datum)
      (var-exp (id) (apply-env env id))
      (texto-lit (text) text)
      (primapp-bin-exp (exp1 prim exp2)
                       (let ((args (list (eval-rand exp1 env) (eval-rand exp2 env))))
                        (apply-primitive-bin prim args)))

      (primapp-un-exp (prim exp)
                      (let ((args (list (eval-rand exp env))))
                     (apply-primitive-un prim args)))
      
      (condicional-exp (test-exp true-exp false-exp)
                       (if (valor-verdad? (evaluar-expresion test-exp env))
                           (evaluar-expresion true-exp env)
                           (evaluar-expresion false-exp env))))))

;; Recibe un operando (expresión) y un ambiente; retorna su valor.
;; Se usa para evaluar los argumentos de las primitivas.
(define eval-rand
  (lambda (rand env)
    (evaluar-expresion rand env)))

;; Recibe el árbol de sintaxis de un programa y evalúa su expresión
;; principal en el ambiente inicial.
(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (un-programa (body)
        (evaluar-expresion body (init-env))
        )
      )
    )
  )

;; ============================================================
;; Interfaz
;; ============================================================

;; Ciclo interactivo (REPL) del lenguaje: muestra "--> ", lee un
;; programa, lo parsea y muestra el resultado de evaluarlo.
(define interpretador
  (sllgen:make-rep-loop "--> "
     (lambda (pgm)
       (evaluar-programa pgm))
       (sllgen:make-stream-parser lexica gramatica)
      )
     )

;; Recibe un programa escrito como texto y retorna el resultado de evaluarlo.
;; Se usa para hacer pruebas sin entrar al ciclo interactivo.
(define probar
  (lambda (texto)
    (evaluar-programa (scan&parse texto))))