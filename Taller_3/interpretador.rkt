#lang eopl

;; Integrantes:
;; ANA SOFIA CANTILLO BOLAÑOS       202610112
;; SARA JULISSA HERNANDEZ HERNANDEZ 202610102
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
   (expresion ("Si" expresion "{" expresion "}" "sino" "{" expresion "}") condicional-exp)
   (expresion ("declarar" "(" (arbno identifier "=" expresion ";") ")" "{" expresion "}") variableLocal-exp)
   (expresion ("procedimiento" "(" (separated-list identifier ",") ")" "{" expresion "}") procedimiento-ex)
   (expresion ("evaluar" expresion "(" (separated-list expresion ",") ")" "finEval") app-exp)

   ;nueva gramática

   (expresion ("declarar-rec" "(" (arbno identifier "(" (separated-list identifier ",") ")" "=" expresion ";") ")" "{" expresion"}") declararRec-exp)
   
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
;;  - recursivo-extendido: Lista de nombres de procedimientos,lista de listas de parámetros,
;;  lista de cuerpos de las funciones y el ambiente anterior

(define-datatype ambiente ambiente?
  (vacio)
  (extendido (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env ambiente?))
  (recursivo-extendido (proc-names (list-of symbol?))
                       (idss (list-of (list-of symbol?)))
                       (bodies (list-of expresion?))
                       (env ambiente?)))
                                   
   

;; Datatype del valor de un procedimiento (ProcVal). Una cerradura guarda:
;;  - lista-ID: la lista de parámetros del procedimiento.
;;  - exp: el cuerpo del procedimiento (sin evaluar).
;;  - amb: el ambiente donde se declaró el procedimiento.
;; Se retorna al evaluar un procedimiento y se usa al aplicarlo.

(define-datatype procVal procVal?
  (cerradura
     (lista-ID(list-of symbol?))
     (exp expresion?)
     (amb ambiente?)))

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
;: Si no está en un ambiente recursivo-extendido y coincide con un procedimiento
;; retorna una cerradura que empaqueta el ambiente recursivo completo.
;; Si no está en el ambiente actual la busca en el anterior, y si
;; llega al ambiente vacío lanza el error de variable inexistente.


(define apply-env
  (lambda (env sym)
    (cases ambiente env
      (vacio ()
                        (eopl:error 'apply-env "Error, la variable no existe ~s" sym))
      (extendido (syms vals envF)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env envF sym))))
    
    (recursivo-extendido (proc-names idss bodies envF)
                         (let ((pos (list-find-position sym proc-names)))
                           (if (number? pos)
                               (cerradura (list-ref idss pos)
                                        (list-ref bodies pos)
                                        env)
                               (apply-env envF sym)))))))



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
;; apply-procedure
;; ============================================================

(define apply-procedure
  (lambda (proc args)
    (cases procVal proc
      (cerradura (lista-ID exp amb)
               (evaluar-expresion exp (extend-env lista-ID args amb))))))

;;Recibe una cerradura (procVal) y la lista de argumentos ya evaluados, y retorna el resultado
;;a evaluar el cuerpo del procedimiento en el ambiente guardado en la cerradura, extendido con
;;los parámteros ligados a los argumentos.



;; ============================================================
;; Evaluación
;; ============================================================

;; Recibe una expresión y un ambiente; retorna el valor de la expresión.
;; Es el corazón del interpretador: decide qué hacer según el tipo
;; de expresión (número, texto, variable o primitiva).
;; app-exp: Evalúa el procedimiento, los argumentos y verifica que sea una cerradura, si no, da error.
;; declararRec-exp : Extiende el ambiente con recursivo-extendido, para permitir 
;; la recursividad en las funciones y evalúa el cuerpo.

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
                           (evaluar-expresion false-exp env)))

      (variableLocal-exp (ids exps cuerpo)
                         (let ((args (eval-rands exps env)))
                           (evaluar-expresion cuerpo
                                              (extend-env ids args env))))

      (app-exp (exp exps)
               (let ((proc (evaluar-expresion exp env))
                     (args (eval-rands exps env)))
                 (if (procVal? proc)
                     (apply-procedure proc args)
                     (eopl:error 'evaluar-expresion
                                 "se aplico algo que no es un procedimiento ~s" proc))))

           
      (procedimiento-ex (ids cuerpo)
                        (cerradura ids cuerpo env))
      
      (declararRec-exp (proc-names idss bodies cuerpo)
                       (evaluar-expresion cuerpo
                                       (recursivo-extendido
                                        proc-names idss bodies env))))))

;; Recibe una lista de operandos (expresiones) y un ambiente; retorna la
;; lista con el valor de cada operando, evaluado en ese ambiente.
;; Se usa para evaluar las expresiones de las variables locales (declarar)
;; antes de extender el ambiente, y luego servirá para los argumentos
;; de los procedimientos.


(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

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

;a) primero necesitamos saber qué tan grande es el número para buscar su representación en base 10
;por ejemplo, si ingresamos el 147, el programa tiene que calcular que como son tres números le toca usar el 100. 
;Entonces, cogemos ese 147 y le empezamos a restar 100.
;Como solo se lo puedo restar una vez, ahí ya tengo guardado mi primer resultado , que es un 1.
;me quedan el 47, Ahora con ese numero, vuelvo a aplicar la misma lógica desde el principio, el programa ve que es de dos dígitos, así que le toca usar el 10.
;Le resto 10 todas las veces que pueda al 47, que van a ser 4 veces, y me termina sobrando un 7. Y ya por último, con ese 7, la escala que toca es el 1, así que lo resto 7 veces hasta que me quede en la nada, en cero.
;Al final, con recursividad es que el programa va a ir arrastrando y sumando ese 1, ese 4 y ese 7 que fuimos sacando en cada pason y que como resultado nos de 12.

(define programa_a
"declarar-rec (
   @ndigits?(@n) = Si (@n >= 10) {(10 * evaluar @ndigits?((@n / 10)) finEval)} sino {1};
   @sumarDigitos(@n) = Si (@n >= evaluar @ndigits?(@n) finEval) {(1 + evaluar @sumarDigitos((@n ~ evaluar @ndigits?(@n) finEval)) finEval)} sino {0};
 )
 {
   evaluar @sumarDigitos( 147 )
   finEval
 }"
)
;b)Primero evaluamos que el número sea mayor a cero, si no, retornamos cero, esa será nuestra base.
;Para los números que sean mayores a cero, lo sumamos junto al mismo programa pasándole como parámetro el mismo número menos 1,
;que volverá a realizar la validación base y, cuando termine, sumará todos los números resultados de cada recursión.
;Por ejemplo, con n=5, como es mayor a 0, 5 lo sumamos con el programa(5-1), eso nos retornará 4 sumado con el programa(4-1), y así hasta que llegue 1-1=0, se acabe la recursión y sume 5+4+3+2+1 igual a 15.

(define programa_b
"declarar-rec (
   @sumaNaturales(@n) = Si (@n > 0) {(@n + evaluar @sumaNaturales((@n ~ 1)) finEval)} sino {0};
 )
 {
   evaluar @sumaNaturales( 5 )
   finEval
 }"
)