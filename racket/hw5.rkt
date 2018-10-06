;; Programming Languages, Homework 5

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for MUPL programs - Do NOT change
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct ifgreater (e1 e2 e3 e4)    #:transparent) ;; if e1 > e2 then e3 else e4
(struct fun  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct call (funexp actual)       #:transparent) ;; function call
(struct mlet (var e body) #:transparent) ;; a local binding (let var = e in body) 
(struct apair (e1 e2)     #:transparent) ;; make a new pair
(struct fst  (e)    #:transparent) ;; get first part of a pair
(struct snd  (e)    #:transparent) ;; get second part of a pair
(struct aunit ()    #:transparent) ;; unit value -- good for ending a list
(struct isaunit (e) #:transparent) ;; evaluate to 1 if e is unit else 0

;; a closure is not in "source" programs but /is/ a MUPL value; it is what functions evaluate to
(struct closure (env fun) #:transparent) 

;; Problem 1

(define (racketlist->mupllist xs)
  (if (null? xs)
      (aunit)
      (apair (car xs) (racketlist->mupllist (cdr xs)))))

(define (mupllist->racketlist es)
  (if (aunit? es)
      null
      (cons (apair-e1 es) (mupllist->racketlist (apair-e2 es)))))

;; Problem 2

;; lookup a variable in an environment
;; Do NOT change this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)]))

;; Do NOT change the two cases given to you.  
;; DO add more cases for other kinds of MUPL expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (envlookup env (var-string e))]
        [(int? e)
         e]
        [(closure? e)
         e]
        [(fun? e)
         e]
        [(add? e) 
         (let ([v1 (eval-under-env (add-e1 e) env)]
               [v2 (eval-under-env (add-e2 e) env)])
           (if (and (int? v1)
                    (int? v2))
               (int (+ (int-num v1) 
                       (int-num v2)))
               (error "MUPL addition applied to non-number")))]
        ;; CHANGE add more cases here
        [(ifgreater? e)
          (let ([v1 (eval-under-env (ifgreater-e1 e) env)]
                [v2 (eval-under-env (ifgreater-e2 e) env)])
            (if (and (int? v1)
                     (int? v2)
                     (> (int-num v1) (int-num v2)))
                (eval-under-env (ifgreater-e3 e) env)
                (eval-under-env (ifgreater-e4 e) env)))]
        [(mlet? e)
         (let ([name (mlet-var e)]
               [v (mlet-e e)])
               (eval-under-env (mlet-body e) (cons (cons name v) env)))]
        [(call? e)
         (let ([my-closure (eval-under-env (call-funexp e) env)])
           (if (closure? my-closure)
               (let* ([func-name (fun-nameopt (closure-fun my-closure))]
                      [arg-name (fun-formal (closure-fun my-closure))]
                      [func-body (fun-body (closure-fun my-closure))]
                      [env-with-arg (cons (cons arg-name (eval-under-env (call-actual e) env)) env)]
                      [final-env  (if func-name
                                      (cons (cons func-name my-closure) env-with-arg)
                                      env-with-arg)])
               (eval-under-env func-body final-env))
             (error "MUPL call applied to non-closure")))]
        [(apair? e)
         (apair (eval-under-env (apair-e1 e) env) (eval-under-env (apair-e2 e) env))]
        [(fst? e)
         (let ([arg (eval-under-env (fst-e e) env)])
           (if (apair? arg)
               (apair-e1 arg)
               (error "MUPL fst applied to non-apair")))]
        [(snd? e)
         (let ([arg (eval-under-env (snd-e e) env)])
           (if (apair? arg)
               (apair-e2 arg)
               (error "MUPL snd applied to non-apair")))]
        [(isaunit? e)
         (let ([arg (eval-under-env (isaunit-e e) env)])
           (if (aunit? arg)
               (int 1)
               (int 0)))]
         [#t (error (format "bad MUPL expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

(define (ifaunit e1 e2 e3)
  (if (aunit? (eval-under-env e1 null))
      (eval-under-env e2 null)
      (eval-under-env e3 null)))

(define (mlet* lst e2)
  (letrec ([f (lambda (prs env) (if (null? prs)
                                  (eval-under-env e2 env)
                                  (let* ([pr (car prs)]
                                         [name (car pr)]
                                         [v (eval-under-env (cdr pr) env)])
                                    (f (cdr prs) (cons (cons name v) env)))))])
    (f lst null)))

(define (ifeq e1 e2 e3 e4)
  (let ([_x (eval-under-env e1 null)]
        [_y (eval-under-env e2 null)])
    (if (= (int-num _x) (int-num _y))
        (eval-under-env e3 null)
        (eval-under-env e4 null))))

;; Problem 4

(define mupl-map
  (fun #f "func"
       (fun "f" "lst"
            (ifaunit (var "lst")
            (aunit)
            (apair (call (var "func") (fst (var "lst")))
                   (call (var "f") (snd (var "lst"))))))))
                                            

(define mupl-mapAddN 
  (mlet "map" mupl-map
        "CHANGE (notice map is now in MUPL scope)"))

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make
;; auto-grading and peer assessment more difficult, so
;; copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))
