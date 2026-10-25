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
  (text ((or letter "_" )(arbno (or letter digit "_" ":"))) string)
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
;; Punto 6:
   ; Gramática BNF
   ;<expresion> ::= procedimiento ( { <identificador> }*(,) ) { <expresion> }
   ;             procedimiento-ex (ids cuerpo)
   (expresion ("procedimiento" "(" (separated-list identifier ",") ")" "{" expresion "}") procedimiento-ex)
;; Punto 7:
   ;Gramática BNF
   ; <expresion> ::= evaluar <expresion> ( { <expresion> }*(,) ) finEval
   ;            app-exp (exp exps)
   (expresion ("evaluar" expresion "(" (separated-list expresion ",") ")" "finEval") app-exp)

   ;Punto 8: nueva gramática
   ;Gramática BNF
   ;<expresion> ::= declarar-rec ( { <identificador> "(" { <identificador> }*(,) ")" "=" <expresion> }*(;) ) { <expresion> }
   ;             declararRec-exp (proc-names idss bodies cuerpo)

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

;; PUNTO 8
  (recursivo-extendido (proc-names (list-of symbol?))
                       (idss (list-of (list-of symbol?)))
                       (bodies (list-of expresion?))
                       (env ambiente?)))
                                   
   

;; Datatype del valor de un procedimiento (ProcVal). Una cerradura guarda:
;;  - lista-ID: la lista de parámetros del procedimiento.
;;  - exp: el cuerpo del procedimiento (sin evaluar).
;;  - amb: el ambiente donde se declaró el procedimiento.
;; Se retorna al evaluar un procedimiento y se usa al aplicarlo.
;; Punto 6
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
;; Si no está en un ambiente recursivo-extendido y coincide con un procedimiento
;; retorna una cerradura que empaqueta el ambiente recursivo completo.
;; Si no está en el ambiente actual la busca en el anterior, y si
;; llega al ambiente vacío lanza el error de variable inexistente.


(define buscar-variable
  (lambda (sym env)
    (cases ambiente env
      (vacio ()
                        (eopl:error 'buscar-variable "Error, la variable no existe ~s" sym))
      (extendido (syms vals envF)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable sym envF))))
      
;; PUNTO 8: Busqueda de procedimientos recursivos
    (recursivo-extendido (proc-names idss bodies envF)
                         (let ((pos (list-find-position sym proc-names)))
                           (if (number? pos)
                               (cerradura (list-ref idss pos)
                                        (list-ref bodies pos)
                                        env)
                               (buscar-variable sym envF)))))))



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

;; Recibe un valor y retorna #f si es el número 0 (entero o decimal, 0 o 0.0) y #t en
;; cualquier otro caso. Define qué es verdadero y qué es falso en el lenguaje.
(define valor-verdad?
  (lambda (exp)
    (not (and (number? exp) (zero? exp)))))

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
;; Punto 7: apply-procedure
;; ============================================================

(define apply-procedure
  (lambda (proc args)
    (cases procVal proc
      (cerradura (lista-ID exp amb)
                 (let ((num-params (length lista-ID))
                       (num-args (length args)))                
                   (if (= num-params num-args)
                       (evaluar-expresion exp (extend-env lista-ID args amb))
                       (eopl:error 'apply-procedure "El procedimiento esperaba ~s argumentos pero recibió ~s"
                                   num-params num-args)))))))
                   
               

;; Recibe un procedimiento (cerradura) y una lista de argumentos (args),
;; valida que el numero de parámetros declarados sea la misma cantidad que los argumentos que se pasen.
;; Y si coinciden evalúa el cuerpo extendiendo el ambiente, y si no coinciden
;; detiene la ejercución arrojando un error.



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
      (var-exp (id) (buscar-variable id env))
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
;; Punto 7: Invocación procedimientos
      (app-exp (exp exps)
               (let ((proc (evaluar-expresion exp env))
                     (args (eval-rands exps env)))
                 (if (procVal? proc)
                     (apply-procedure proc args)
                     (eopl:error 'evaluar-expresion
                                 "se aplico algo que no es un procedimiento ~s" proc))))

;; Punto 6: Creación de procedimientos
      (procedimiento-ex (ids cuerpo)
                        (cerradura ids cuerpo env))

;; PUNTO 8: Evaluación declararRec-exp
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

;; PUNTO 9.a) @sumarDigitos(n): suma los dígitos de un entero positivo sin usar módulo ni
;; división entera, solo restas, comparaciones y recursión.
;;
;; Idea: cada dígito d de un número, ubicado en la posición de una potencia de 10 p,
;; equivale a restar p exactamente d veces. Por eso, el total de restas que se hacen
;; (de la potencia más grande a la más pequeña) es igual a la suma de los dígitos.
;;
;; @potencia10(n): retorna la mayor potencia de 10 que no supera a n. Si n tiene
;; más de una cifra (n >= 10), multiplica por 10 el resultado de llamarse con n / 10;
;; si no, retorna 1 (10^0). Ejemplo: para 147 -> 10 * (10 * 1) = 100.
;;
;; @sumarDigitos(n): calcula p = @potencia10(n). Si n >= p, todavía cabe una resta:
;; retorna 1 + @sumarDigitos(n - p). Si n < p, retorna 0. La comparación usa >=
;; porque cuando n es igual a p (por ejemplo 10 con p = 10) aún cabe una resta.
;; Como se recalcula la potencia de 10 en cada llamada, al bajar el número a un
;; tamaño menor, la potencia se ajusta sola (si queda un 0 intermedio, ese dígito
;; simplemente aporta 0 restas).
;;
;; Ejemplo con 147:
;;   p = 100 -> 1 resta  -> queda 47
;;   p = 10  -> 4 restas -> queda 7
;;   p = 1   -> 7 restas -> queda 0
;;   total de restas = 1 + 4 + 7 = 12

;; Prueba rápida: (probar programa_a)
(define programa_a
"declarar-rec (
   @potencia10(@n) = Si (@n >= 10) {(10 * evaluar @potencia10((@n / 10)) finEval)} sino {1};
   @sumarDigitos(@n) = Si (@n >= evaluar @potencia10(@n) finEval) {(1 + evaluar @sumarDigitos((@n ~ evaluar @potencia10(@n) finEval)) finEval)} sino {0};
 )
 {
   evaluar @sumarDigitos( 147 )
   finEval
 }"
)
;; Texto limpio de programa_a: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar-rec ( @potencia10(@n) = Si (@n >= 10) {(10 * evaluar @potencia10((@n / 10)) finEval)} sino {1}; @sumarDigitos(@n) = Si (@n >= evaluar @potencia10(@n) finEval) {(1 + evaluar @sumarDigitos((@n ~ evaluar @potencia10(@n) finEval)) finEval)} sino {0}; ) { evaluar @sumarDigitos( 147 ) finEval }
|#

;; PUNTO 9.b) @sumaNaturales(n): calcula la suma de los primeros n enteros positivos
;; de forma recursiva. Los dos programas (programa_b5 y programa_b10) usan el mismo
;; procedimiento; solo cambia el valor con el que se llama (n=5 y n=10).
;;
;; Caso base: si n no es mayor que 0, retorna 0. Es el neutro de la suma, así que
;; no altera el total. Esta guarda también evita que la recursión baje para siempre
;; si llegara un número negativo.
;; Caso recursivo: si n es mayor que 0, retorna n sumado con el resultado de
;; @sumaNaturales(n - 1), que repite la misma validación con un número menor.
;;
;; Ejemplo con n=5: 5 + @sumaNaturales(4), luego 4 + @sumaNaturales(3), y así hasta
;; @sumaNaturales(1) = 1 + @sumaNaturales(0), donde se llega al caso base y retorna 0.
;; Al regresar, las sumas se juntan: 5 + 4 + 3 + 2 + 1 + 0 = 15.
;; Con n=10 ocurre lo mismo hasta 10 + 9 + ... + 1 + 0 = 55.

;; Prueba rápida: (probar programa_b5)
(define programa_b5
"declarar-rec (
   @sumaNaturales(@n) = Si (@n > 0) {(@n + evaluar @sumaNaturales((@n ~ 1)) finEval)} sino {0};
 )
 {
   evaluar @sumaNaturales( 5 )
   finEval
 }"
)
;; Texto limpio de programa_b5: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar-rec ( @sumaNaturales(@n) = Si (@n > 0) {(@n + evaluar @sumaNaturales((@n ~ 1)) finEval)} sino {0}; ) { evaluar @sumaNaturales( 5 ) finEval }
|#

;; Prueba rápida: (probar programa_b10)
(define programa_b10
"declarar-rec (
   @sumaNaturales(@n) = Si (@n > 0) {(@n + evaluar @sumaNaturales((@n ~ 1)) finEval)} sino {0};
 )
 {
   evaluar @sumaNaturales( 10 )
   finEval
 }"
)
;; Texto limpio de programa_b10: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar-rec ( @sumaNaturales(@n) = Si (@n > 0) {(@n + evaluar @sumaNaturales((@n ~ 1)) finEval)} sino {0}; ) { evaluar @sumaNaturales( 10 ) finEval }
|#

;; PUNTO 9.c) @multiplicar(a,b): calcula el producto de dos enteros no negativos mediante
;; sumas sucesivas, sin usar la primitiva de multiplicación (*) en ningún punto.
;; Es recursivo: @multiplicar se llama a sí mismo.
;;
;; Caso base: si b no es mayor que 0, retorna 0. Es el neutro de la suma, y cubre
;; también el caso en que a sea 0 (todas las sumas darían 0).
;; Caso recursivo: si b es mayor que 0, retorna a sumado con el resultado de
;; @multiplicar(a, b - 1). El parámetro a se mantiene igual y b baja de uno en uno,
;; así que la recursión se acerca siempre al caso base.
;;
;; Ejemplo con (4,3): 4 + @multiplicar(4,2)
;;   @multiplicar(4,2) = 4 + @multiplicar(4,1)
;;   @multiplicar(4,1) = 4 + @multiplicar(4,0)
;;   @multiplicar(4,0) = 0   (caso base)
;; Al regresar: 4 + 4 + 4 + 0 = 12.

;; Prueba rápida: (probar programa_c)
(define programa_c
"declarar-rec (
   @multiplicar(@a,@b) = Si (@b > 0) {(@a + evaluar @multiplicar(@a,(@b ~ 1)) finEval)} sino {0};
 )
 {
   evaluar @multiplicar( 4,3 )
   finEval
 }"
)
;; Texto limpio de programa_c: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar-rec ( @multiplicar(@a,@b) = Si (@b > 0) {(@a + evaluar @multiplicar(@a,(@b ~ 1)) finEval)} sino {0}; ) { evaluar @multiplicar( 4,3 ) finEval }
|#

;; PUNTO 9.d) sumaParesRango
;; El programa divide el problema en dos partes: verificar si un número es par
;; (@esPar?) y recorrer un rango sumando solo los pares (@sumaParesRango).
;; No usa módulo ni división: solo restas, comparaciones, add1 y la suma del
;; acumulado.
;;
;; @esPar?(n): sigue la definición inductiva de los múltiplos de 2. Un número n
;; es par si n = 0 (caso base, retorna 1) o si n - 2 es par. Antes de llamarse,
;; comprueba que n - 2 no sea negativo; si lo fuera (les pasa a los impares,
;; que llegan a 1), el número no es par y retorna 0 (falso).
;;
;; @sumaParesRango(a,b): mientras se cumpla a <= b, evalúa si a es par con
;; @esPar?; si lo es, suma a con el resultado de recorrer el rango desde el
;; siguiente número (add1 de a, con el mismo b); si no, simplemente pasa al
;; siguiente sin sumar. Cuando a supera a b, la condición a <= b deja de
;; cumplirse, la recursión termina y retorna 0.
;;
;; Ejemplo con el rango (2,7):
;; Para el 2: @esPar? confirma que es par, así que se suma con el resultado de
;; evaluar el programa desde el siguiente número (3).
;; Para el 3: @esPar? dice que no es par, no se suma y se pasa al 4.
;; Para el 4: es par, se suma (4 + ...). El 5 se ignora, el 6 se suma y el 7
;; se ignora.
;; Al llegar al 8, como 8 es mayor que 7 (@b), termina y retorna 0.
;; La recursión junta lo acumulado: 2 + 4 + 6 + 0 = 12.

;; Prueba rápida: (probar programa_d)
(define programa_d
"declarar-rec (
   @esPar?(@n) = Si (@n == 0) {1} sino { Si ((@n ~ 2) >= 0) { evaluar @esPar?((@n ~ 2)) finEval } sino {0} };
   @sumaParesRango(@a,@b) = Si (@a <= @b) { Si evaluar @esPar?(@a) finEval {(@a + evaluar @sumaParesRango(add1(@a),@b) finEval)} sino {evaluar @sumaParesRango(add1(@a),@b) finEval}} sino {0};
 )
 {
   evaluar @sumaParesRango( 2,7 )
   finEval
 }"
)
;; Texto limpio de programa_d: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar-rec ( @esPar?(@n) = Si (@n == 0) {1} sino { Si ((@n ~ 2) >= 0) { evaluar @esPar?((@n ~ 2)) finEval } sino {0} }; @sumaParesRango(@a,@b) = Si (@a <= @b) { Si evaluar @esPar?(@a) finEval {(@a + evaluar @sumaParesRango(add1(@a),@b) finEval)} sino {evaluar @sumaParesRango(add1(@a),@b) finEval}} sino {0}; ) { evaluar @sumaParesRango( 2,7 ) finEval }
|#

;; PUNTO 9.e) @saludar: decorador
;; El programa usa el concepto de decorador: un procedimiento que recibe otro
;; procedimiento y retorna uno nuevo que hace lo mismo que el original, pero
;; agregándole algo (aquí, el saludo "Hola:" al inicio).
;;
;; @integrantes: procedimiento sin parámetros que retorna el texto con los
;; nombres del grupo, "Sofia_Sara_y_Daniel".
;;
;; @saludar(@proSaludar): recibe un procedimiento, @proSaludar, y no ejecuta
;; nada por sí mismo: retorna un procedimiento nuevo (sin parámetros) que, al
;; invocarse, llama a @proSaludar con evaluar @proSaludar() finEval y
;; concatena con concat el texto "Hola:" delante de lo que ese procedimiento
;; retorne.
;;
;; @decorate: no se escribe a mano, se obtiene llamando a @saludar con
;; @integrantes: evaluar @saludar(@integrantes) finEval. Se pasa
;; @integrantes sin evaluar, es decir, el procedimiento mismo y no su
;; resultado. El valor de @decorate es el procedimiento nuevo que retornó
;; @saludar.
;;
;; Se usan dos declarar anidados: las expresiones de un declarar se evalúan en
;; el ambiente de afuera, así que @decorate no vería a @saludar ni a
;; @integrantes si se definiera en el mismo declarar. Por eso va en el
;; declarar interior.
;;
;; Ejemplo:
;; Al evaluar @saludar(@integrantes) se crea un ambiente donde @proSaludar es
;; @integrantes, y se retorna una cerradura que guarda ese ambiente. Esa
;; cerradura es @decorate.
;; Al invocar @decorate( ), su cuerpo busca @proSaludar en el ambiente que
;; guardó la cerradura (aunque @saludar ya terminó) y lo llama, obteniendo
;; "Sofia_Sara_y_Daniel".
;; Luego concat le pone "Hola:" delante, y el resultado es
;; "Hola:Sofia_Sara_y_Daniel".

;; Prueba rápida: (probar programa_e)
(define programa_e
"declarar (
     @integrantes = procedimiento () {\"Sofia_Sara_y_Daniel\"};
     @saludar = procedimiento (@proSaludar) {procedimiento () {(\"Hola:\" concat evaluar @proSaludar() finEval)}};
   )
   {
      declarar (@decorate = evaluar @saludar(@integrantes) finEval;)
      {
        evaluar @decorate( ) finEval
      }
   }"
)
;; Texto limpio de programa_e: copiar SOLO la línea de abajo y pegarla en el intérprete (-->)
#|
declarar ( @integrantes = procedimiento () {"Sofia_Sara_y_Daniel"}; @saludar = procedimiento (@proSaludar) {procedimiento () {("Hola:" concat evaluar @proSaludar() finEval)}}; ) { declarar (@decorate = evaluar @saludar(@integrantes) finEval;) { evaluar @decorate( ) finEval } }
|#

;; PUNTO 9.f) @saludar con mensaje al final: decorador con parámetro
;; El programa extiende el concepto de decorador del punto e: un procedimiento
;; que recibe otro procedimiento y retorna uno nuevo que, además de agregar el
;; prefijo "Hola:" al inicio, acepta un argumento adicional (@finalMsg) para
;; concatenarlo al final de todo el texto.

;; @integrantes: procedimiento sin parámetros que retorna el texto con los
;; nombres base, "Robinson_y_Sara".

;; @saludar(@proSaludar): recibe un procedimiento, @proSaludar, y no ejecuta
;; nada por sí mismo: retorna un procedimiento nuevo que espera el parámetro
;; @finalMsg. Al invocarse, llama a @proSaludar con evaluar @proSaludar() finEval,
;; le concatena "Hola:" adelante y luego concatena el valor de @finalMsg al
;; final mediante dos operaciones concat anidadas.

;; @decorate: no se escribe a mano, se obtiene llamando a @saludar con
;; @integrantes: evaluar @saludar(@integrantes) finEval. Se pasa
;; @integrantes sin evaluar, es decir, el procedimiento mismo y no su
;; resultado. El valor de @decorate es el procedimiento nuevo (que espera
;; un parámetro) retornado por @saludar.
;;
;; Se usan dos declarar anidados: las expresiones de un declarar se evalúan en
;; el ambiente de afuera, así que @decorate no vería a @saludar ni a
;; @integrantes si se definiera en el mismo declarar. Por eso va en el
;; declarar interior.

;; Al invocar @decorate("_ProfesoresFLP"), el parámetro @finalMsg recibe el
;; texto "_ProfesoresFLP". El cuerpo de la cerradura busca @proSaludar en el
;; ambiente guardado y lo llama, obteniendo "Robinson_y_Sara".
;; El primer concat genera "Hola:Robinson_y_Sara", y el segundo concat le
;; añade "_ProfesoresFLP" al final, dando como resultado
;; "Hola:Robinson_y_Sara_ProfesoresFLP".

;; Prueba rápida: (probar programa_f)
(define programa_f
"declarar (
     @integrantes = procedimiento () {\"Robinson_y_Sara\"};
     @saludar = procedimiento (@proSaludar) { procedimiento (@finalMsg) {((\"Hola:\" concat evaluar @proSaludar() finEval) concat @finalMsg)}};
   )
   {
      declarar (@decorate = evaluar @saludar(@integrantes) finEval;)
      {
        evaluar @decorate(\"_ProfesoresFLP\") finEval
      }
   }"
)
;; Prueba para el intérprete (-->)
#|
declarar ( @integrantes = procedimiento () {"Robinson_y_Sara"}; @saludar = procedimiento (@proSaludar) { procedimiento (@finalMsg) {(("Hola:" concat evaluar @proSaludar() finEval) concat @finalMsg)}}; ) { declarar (@decorate = evaluar @saludar(@integrantes) finEval;) { evaluar @decorate("_ProfesoresFLP") finEval } }
|#
  
  
  