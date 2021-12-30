(module interp (lib "eopl.ss" "eopl")
  
  ;; interpreter for the EXPLICIT-REFS language

  (require "drscheme-init.scm")

  (require "lang.scm")
  (require "data-structures.scm")
  (require "environments.scm")
  (require "store.scm")
  
  (provide value-of-program value-of instrument-let instrument-newref)

  ;;;;;;;;;;;;;;;; switches for instrument-let ;;;;;;;;;;;;;;;;

  (define instrument-let (make-parameter #f))

  ;; say (instrument-let #t) to turn instrumentation on.
  ;;     (instrument-let #f) to turn it off again.

  ;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

  ;; value-of-program : Program -> ExpVal
  ;; Page: 110
  (define value-of-program 
    (lambda (pgm)
      (initialize-store!)               ; new for explicit refs.
      (cases program pgm
        (a-program (exp1)
                   (value-of exp1 (init-env))))))

  ;; value-of : Exp * Env -> ExpVal
  ;; Page: 113
  (define value-of
    (lambda (exp env)
      (cases expression exp

        ;\commentbox{ (value-of (const-exp \n{}) \r) = \n{}}
        (const-exp (num) (num-val num))

        ;\commentbox{ (value-of (var-exp \x{}) \r) = (apply-env \r \x{})}
        (var-exp (var) (apply-env env var))

        ;\commentbox{\diffspec}
        (diff-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (let ((num1 (expval->num val1))
                          (num2 (expval->num val2)))
                      (num-val
                       (- num1 num2)))))
      
        ;\commentbox{\zerotestspec}
        (zero?-exp (exp1)
                   (let ((val1 (value-of exp1 env)))
                     (let ((num1 (expval->num val1)))
                       (if (zero? num1)
                           (bool-val #t)
                           (bool-val #f)))))
              
        ;\commentbox{\ma{\theifspec}}
        (if-exp (exp1 exp2 exp3)
                (let ((val1 (value-of exp1 env)))
                  (if (expval->bool val1)
                      (value-of exp2 env)
                      (value-of exp3 env))))

        ;\commentbox{\ma{\theletspecsplit}}
        (let-exp (var exp1 body)       
                 (let ((val1 (value-of exp1 env)))
                   (value-of body
                             (extend-env var val1 env))))
        
        (proc-exp (var body)
                  (proc-val (procedure var body env)))

        (call-exp (rator rand)
                  (let ((proc (expval->proc (value-of rator env)))
                        (arg (value-of rand env)))
                    (apply-procedure proc arg)))

        (letrec-exp (p-names b-vars p-bodies letrec-body)
                    (value-of letrec-body
                              (extend-env-rec* p-names b-vars p-bodies env)))

        (begin-exp (exp1 exps)
                   (letrec 
                       ((value-of-begins
                         (lambda (e1 es)
                           (let ((v1 (value-of e1 env)))
                             (if (null? es)
                                 v1
                                 (value-of-begins (car es) (cdr es)))))))
                     (value-of-begins exp1 exps)))

        (newref-exp (exp1)
                    (let ((v1 (value-of exp1 env)))
                      (ref-val (newref v1))))

        (deref-exp (exp1)
                   (let ((v1 (value-of exp1 env)))
                     (let ((ref1 (expval->ref v1)))
                       (deref ref1))))

        (setref-exp (exp1 exp2)
                    (let ((ref (expval->ref (value-of exp1 env))))
                      (let ((v2 (value-of exp2 env)))
                        (begin
                          (setref! ref v2)
                          (num-val 23)))))

        ; #####################################################
        ; ###### ENTER YOUR CODE HERE
        ; ###### value-of cases for new expressions, remember
        ; ###### that you need to use memory functionalities. 
        ; #####################################################

        (new-arr-exp (exp1 exp2)
                     (let ((length (expval->num (value-of exp1 env)))
                           (value (value-of exp2 env)))
                       (arr-val (array-value (new-arr-helper length value)))))

        (update-arr-exp (exp1 exp2 exp3)
                        (let ((arr (expval->arr (value-of exp1 env)))
                              (index (expval->num (value-of exp2 env)))
                              (value (value-of exp3 env)))
                          (update-arr-helper arr index value)))

        (read-arr-exp (exp1 exp2)
                      (let ((arr (expval->arr (value-of exp1 env)))
                            (index (expval->num (value-of exp2 env))))
                        (read-arr-helper arr index)))

        (print-arr-exp (exp1)
                       (let ((arr (expval->arr (value-of exp1 env))))
                         (print-arr-helper arr)))

        ; Creates new stack with initial values.
        ; Stack size is set to 1023 since at most 1000 consecutive pushes can occur
        ; Stack initial value is set to -1 since it represents the empty stack value given in the pdf
        (newstack-exp ()
                      (let ((stack-size 1023)
                            (stack-init-value (num-val -1)))
                        (let ((created-stack (new-arr-helper stack-size stack-init-value)))
                          (arr-val (array-value created-stack)))))
        
        ; Performs push operation on given stack with given value
        ; We find the top of the stack by checking the first -1 value
        ; Then we call setref! of that location with given value
        (stack-push-exp (exp1 exp2)
                        (let ((stack (expval->arr (value-of exp1 env)))
                              (val (value-of exp2 env)))
                          (update-arr-helper stack (get-last-helper stack) val)))

        (stack-pop-exp (exp1)
                       (let ((stack (expval->arr (value-of exp1 env))))
                         (let ((top-val (read-arr-helper stack (get-pop-helper stack))))
                           (begin
                             (update-arr-helper stack (get-pop-helper stack) (num-val -1))
                             top-val))))

        (stack-size-exp (exp1)
                        (let ((stack (expval->arr (value-of exp1 env))))
                          (num-val (+ 1 (get-pop-helper stack)))))

        (stack-top-exp (exp1)
                       (let ((stack (expval->arr (value-of exp1 env))))
                         (let ((top-val (read-arr-helper stack (get-pop-helper stack))))
                           top-val)))
        
        (empty-stack?-exp (exp1)
                          (let ((stack (expval->arr (value-of exp1 env))))
                            (bool-val (empty-helper stack))))
        (print-stack-exp (exp1)
                         (let ((stack (expval->arr (value-of exp1 env))))
                           (print-arr-helper stack)))
                        
                             
                           
    
        ; #####################################################
        )))

  ; ###### YOU CAN WRITE HELPER FUNCTIONS HERE

  ; Creates an array with the created references by returned newref call.
  (define (new-arr-helper length value)
    (if (= length 0)
        (list)
        (cons (newref value) (new-arr-helper (- length 1) value))))

  ; Updates an array with the given index / value pair.
  (define (update-arr-helper arr index value)
    (cases arrval arr
      (array-value (elements)
                   (setref! (list-ref elements index) value))))

  ; Reads an element of the array in the given index.
  (define (read-arr-helper arr index)
    (cases arrval arr
      (array-value (elements) (deref (list-ref elements index)))))

  ; Prints all elements seperated by the space char.
  ; P.S. We returned 23 as a return value, since it is specified on the lecture slides.
  (define (print-arr-helper arr)
    (cases arrval arr
      (array-value (elements) (print-each-element elements))))

  ; Prints the each element in the given list.
  ; P. S. Since we are storing the list of references,
  ; we are taking list as an input.
  (define (print-each-element l)
    (if (null? l)
        ; Default value for ending, same as return 0 in the other programming languages.
        (num-val 23)
        (begin
          (display (deref (car l)))
          (display " ")
          (print-each-element (cdr l)))))
  
  ; Gets the index of the top of the stack by using get-last-index helper method
  (define (get-last-helper stack)
    (cases arrval stack
      (array-value (elements) (get-last-index elements 0))))

  ; Used in get-last-helper to get the index of top element
  (define (get-last-index l counter)
    (if (null? l)
        -1
        (if (= (expval->num (deref (car l))) -1)
            counter
            (get-last-index (cdr l) (+ 1 counter)))))
  
  ; Gets the element that is going to be popped
  (define (get-pop-helper stack)
    (cases arrval stack
      (array-value (elements) (get-pop-index elements 0))))
  
  ; Returns the index of the element that is going to be popped
  ; Used in get-pop-helper to pop element
  (define (get-pop-index l counter)
    (if (null? l)
        -1
        (if (= (expval->num (deref (car l))) -1)
            -1
            (if (null? (cdr l))
                0
                (if (= (expval->num (deref (cadr l))) -1)
                    counter
                    (get-pop-index (cdr l) (+ counter 1)))))))
  
  ; Checks if the given stack is empty or not using helper method of check-empty
  (define (empty-helper stack)
                        (cases arrval stack
                          (array-value (elements) (check-empty elements))))

  ; This method returns true when the given stack is null,
  ; otherwise returns false
  (define (check-empty l)
    (if (null? l)
        #t
        (if (= -1 (expval->num (deref (car l))))
            #t
            #f)))
        
  
    ;; apply-procedure : Proc * ExpVal -> ExpVal
    ;; 
    ;; uninstrumented version
    ;;   (define apply-procedure
    ;;    (lambda (proc1 arg)
    ;;      (cases proc proc1
    ;;        (procedure (bvar body saved-env)
    ;;          (value-of body (extend-env bvar arg saved-env))))))

    ;; instrumented version
    (define apply-procedure
      (lambda (proc1 arg)
        (cases proc proc1
          (procedure (var body saved-env)
                     (let ((r arg))
                       (let ((new-env (extend-env var r saved-env)))
                         (when (instrument-let)
                           (begin
                             (eopl:printf
                              "entering body of proc ~s with env =~%"
                              var)
                             (pretty-print (env->list new-env))
                             (eopl:printf "store =~%")
                             (pretty-print (store->readable (get-store-as-list)))
                             (eopl:printf "~%")))
                         (value-of body new-env)))))))


    ;; store->readable : Listof(List(Ref,Expval)) 
    ;;                    -> Listof(List(Ref,Something-Readable))
    (define store->readable
      (lambda (l)
        (map
         (lambda (p)
           (cons
            (car p)
            (expval->printable (cadr p))))
         l)))
 
    )
  


  
  