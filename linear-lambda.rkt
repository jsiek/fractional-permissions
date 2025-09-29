#lang racket

(require racket/match racket/dict rackunit rebellion/collection/multiset)

;; Author: Jeremy Siek

;; This is adapted from the linear lambda calculus in the book chapter
;; Substructural Type Systems
;; by David Walker
;; in the book Advanced Topics in Types and Programming Languages
;; edited by Benjamin C. Pierce.

;; Changes:
;; * Move dynamic qualifiers from the heap to the addresses.
;; * Add fractional permissions.

;; Syntax
;;
;; n     numbers
;; b     booleans
;; k     ::= n | b        constants
;; x,y   variables
;;
;; addr  ::= (q n)
;; intro ::= k | (lambda (x) e) | (pair e e) | (op e ...)
;; op ::= + | - | equal?
;; q ::= lin | un | (frac n)                           dynamic qualifier
;; e ::= (q intro) | x | (e e)                         expression
;;     | (split e (x y) e)
;;     | (dup e) | (join e e)
;;     | (write e1 e2 (x) e3)      TODO: e1 produces an address, write value of e2 into the address, then
;;                                 put the address in variable x, which can be used in e3.
;; v ::= k | (lambda (x) e) | (pair v v)               value
;; heap : dict[nat,value]
;; env  : dict[variable,addr]

;; q ::= lin | un | frac                 static qualifier
;; P ::= bool | int | (-> T T)           pretypes
;; T ::= (q P)                           types



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Interpreter

(define (constant? k)
  (or (integer? k) (boolean? k)))

(define (operator? op) (memq op '(+ - zero?)))

;; delta interprets operators
;; cs : list[value]
;; returns value
(define delta
  (lambda (op vs)
    (match op
      ['+ (apply + vs)]
      ['- (apply - vs)]
      ['zero? (apply equal? vs)]
      [else
       (error 'delta "unmatched ~s" op)]
      )))

(define (qualifier? q)
  (match q
    ['lin #t]
    ['un #t]
    [`(frac ,f) #t]
    [else #f]))

(define (address-of addr)
  (match addr
    [`((frac ,f) ,n) #:when (equal? f 0)
     (error 'address-of "you may not access address with zero fractional permission")]
    [`(,q ,n) n]
    ))

(define (qualifier-of addr)
  (match addr
    [`(,q ,n) q]
    ))

(define (alloc heap q val)
  (let ([address (length heap)])
    (values (list q address) (dict-set heap address val))))

(define (dealloc heap addr)
  (match addr
    [`(lin ,n) (dict-remove heap n)]
    [`((frac 1) ,n) (dict-remove heap n)]
    [`((frac ,f) ,n) heap]
    [`(un ,n) heap]))

(define (read heap addr)
  (define n (address-of addr))
  (dict-ref heap n))

(define (write heap addr val)
  (define n (address-of addr))
  (dict-set heap n val))


;; env : variable -> address
;; exp : expression
;; returns value
(define (interp-intro env heap exp)
  (match exp
    [k #:when (constant? k)
       (values k heap)]
    [`(lambda (,x : ,T) ,e)
     (values `(closure ,x ,e ,env) heap)]
    [`(pair ,e1 ,e2)
     (define-values (v1 heap1) (interp env heap e1))
     (define-values (v2 heap2) (interp env heap1 e2))
     (values `(pair ,v1 ,v2) heap2)]
    [`(,op ,args ...) #:when (operator? op)
     (define-values (arg-vals new-heap)
       (for/fold ([arg-vals '()]
                  [current-heap heap]
                  #:result (values arg-vals current-heap))
                 ([arg args])
                 (define-values (arg-addr heap^) (interp env current-heap arg))
                 (values (cons (read heap^ arg-addr) arg-vals)
                         (dealloc heap^ arg-addr))))
     (values (delta op arg-vals) new-heap)]
    [else
     (error 'interp-intro "expected an introduction form, not ~a" exp)]))


;; env : variable -> address
;; heap : address -> value
;; exp : expression
;; returns address * heap
(define (interp env heap exp)
  (match exp
    [x #:when (symbol? x)
       (values (dict-ref env x) heap)]
    
    [`(,q ,intro) #:when (qualifier? q)
     (define-values (pv heap^) (interp-intro env heap intro))
     (alloc heap^ q pv)]

    [`(if ,cond ,thn ,els)
     (define-values (cond-addr heap1) (interp env heap cond))
     (define cond-val (read heap1 cond-addr))
     (match cond-val
       [#t
        (interp env (dealloc heap1 cond-addr) thn)]
       [#f
        (interp env (dealloc heap1 cond-addr) els)]
       [else
        (error 'interp "expected boolean in condition of if, not ~a" cond)]
       )]
     
    [`(split ,e1 (,x ,y) ,e2)
     (define-values (addr heap1) (interp env heap e1))
     (match (read heap1 addr)
       [`(pair ,v1 ,v2)
        (define env^ (dict-set (dict-set env x v1) y v2))
        (interp env^ (dealloc heap1 addr) e2)]
       [else
        (error 'interp "expected to split a pair, not ~a"
               (read heap1 addr))])]

    [`(dup ,e)
     (define-values (addr heap1) (interp env heap e))
     (match addr
       [`((frac ,f) ,n)
        (alloc heap1 'lin `(pair ((frac ,(/ f 2)) ,n) ((frac ,(/ f 2)) ,n)))]
       [else
        (error 'interp "expected to dup a fractional address, not ~a" addr)])]

    [`(join ,e1 ,e2)
     (define-values (addr1 heap1) (interp env heap e1))
     (define-values (addr2 heap2) (interp env heap1 e2))
     (match (list addr1 addr2)
       [`(((frac ,f1) ,n1) ((frac ,f2) ,n2))
        (if (not (equal? n1 n2))
            (error 'interp "join expected two pointers to the same address, ~a != ~a" n1 n2)
            (void))
        (values `((frac ,(+ f1 f2)) ,n1) heap2)]
       [else
        (error 'interp "join expected fractional addresses, not ~a and ~a" addr1 addr2)])]
    
    [`(,e1 ,e2)
     (define-values (rator-addr heap1) (interp env heap e1))
     (define-values (rand-addr heap2) (interp env heap1 e2))
     (define clos (read heap1 rator-addr))
     (match clos
       [`(closure ,x ,body ,env^)
        (interp (dict-set env^ x rand-addr)
                (dealloc heap2 rator-addr)
                body)]
       [else
        (error 'interp "bad function value in application ~a" clos)])]
    
    [else
     (error 'interp "unrecognized expression ~a" exp)]
    ))

(define (run program)
  (define-values (T FV) (type-check '() program))
  (check-true (or (equal? T `(lin int)) (equal? T `(un int))))
  (check-true (equal? (multiset-size FV) 0))
  (define-values (addr heap) (interp '() '() program))
  (read heap addr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Type Checker

(define (delta-type-check op arg-types)
  (define raw-arg-types (for/list ([T arg-types])
                                  (match T
                                    [`(,q ,P) P])))
  (match op
    ['+
     (if (not (equal? raw-arg-types '(int int)))
         (error 'type-check "operator + expects integer arguments, not ~a" raw-arg-types)
         'int)]
    ['-
     (if (not (equal? raw-arg-types '(int int)))
         (error 'type-check "operator - expects integer arguments, not ~a" raw-arg-types)
         'int)]
    ['zero?
     (if (not (equal? raw-arg-types '(int)))
         (error 'type-check "zero? expects an integer argument, not ~a" raw-arg-types)
         'bool)]
    [else
     (error 'delta-type-check "unrecognized opereator ~a" op)]))

;; returns type and the multiset of free variables
(define (type-check-intro env exp)
  (match exp
    [k #:when (integer? k)
       (values 'int (multiset))]
    
    [k #:when (boolean? k)
       (values 'bool (multiset))]
    
    [`(lambda (,x : ,S) ,e)
     (define-values (T FV) (type-check (dict-set env x S) e))
     (match S
       [`(lin ,P)
        (if (> (multiset-frequency FV x) 1)
            (error 'type-check "linear variable ~a used more than once" x)
            (void))]
       [`(frac ,P)
        (if (> (multiset-frequency FV x) 1)
            (error 'type-check "fractional variable ~a used more than once" x)
            (void))]
       [else (void)])
     (values `(-> ,S ,T) (multiset-remove FV x 	#:copies +inf.0))]
    
    [`(pair ,e1 ,e2)
     (define-values (T1 FV1) (type-check env e1))
     (define-values (T2 FV2) (type-check env e2))
     (values `(pair ,T1 ,T2) (multiset-add-all FV1 FV2))]

    [`(,op ,args ...) #:when (operator? op)
     (define arg-tys '())
     (define FVs (multiset))
     (for ([arg args])
          (define-values (P FV) (type-check env arg))
          (set! arg-tys (cons P arg-tys))
          (set! FVs (multiset-add-all FVs FV)))
     (values (delta-type-check op arg-tys) FVs)]
    
    [else
     (error 'type-check-intro "expected an introduction form, not ~a" exp)]))

(define (type-check env exp)
  (match exp
    [x #:when (symbol? x)
       (values (dict-ref env x) (multiset x))]

    [`(un ,intro)
     (define-values (P FV) (type-check-intro env intro))
     (for ([x (in-multiset FV)])
          (match (dict-ref env x)
            [`(lin ,P)
             (error 'type-check "can't refer to linear variables inside unrestricted function")]
            [`((frac ,f) ,P)
             (error 'type-check "can't refer to fractional variables inside unrestricted function")]
            [else
             (void)]))
     (values `(un ,P) FV)]

    [`(lin ,intro)
     (define-values (P FV) (type-check-intro env intro))
     (values `(lin ,P) FV)]

    [`((frac ,f) ,intro)
     (define-values (P FV) (type-check-intro env intro))
     (values `(frac ,P) FV)]
    
    [`(if ,cond ,thn ,els)
     (define-values (P-cond FV-cond) (type-check env cond))
     (define-values (P-thn FV-thn) (type-check env thn))
     (define-values (P-els FV-els) (type-check env els))
     (if (not (equal? P-thn P-els))
         (error 'type-check "branches of 'if' must have same type, not\n\t~a\nand\n\t~a" P-thn P-els)
         (void))
     (values P-thn (multiset-add-all (multiset-add-all FV-cond FV-thn) FV-els))]
    
    [`(split ,e1 (,x ,y) ,e2)
     (define-values (T1 FV1) (type-check env e1))
     (match T1
       [`(,q1 (pair ,S ,T))
        (define env^ (dict-set (dict-set env x S) y T))
        (define-values (T2 FV2) (type-check env^ e2))
        (values T2 (multiset-remove (multiset-remove FV2 x #:copies +inf.0)
                                    y #:copies +inf.0))]
       [else
        (error 'type-check "expected to split a pair, not ~a" T1)])]

    [`(dup ,e)
     (define-values (T FV) (type-check env e))
     (match T
       [`(frac ,P)
        (values `(lin (pair (frac ,P) (frac ,P)))
                FV)]
       [else
        (error 'type-check
               "expected to duplicate a fractional reference, not ~a" T)])]

    [`(join ,e1 ,e2)
     (define-values (T1 FV1) (type-check env e1))
     (define-values (T2 FV2) (type-check env e2))
     (match (list T1 T2)
       [`((frac ,P1) (frac ,P2)) #:when (equal? P1 P2)
        (values `(frac ,P1)
                (multiset-add-all FV1 FV2))]
       [else
        (error 'type-check "cannot join ~a and ~a" T1 T2)])]
    
    [`(,e1 ,e2)
     (define-values (T-rator FV-rator) (type-check env e1))
     (define-values (T-rand FV-rand) (type-check env e2))
     (match T-rator
       [`(,q1 (-> ,S ,T))
        (if (not (equal? S T-rand))
            (error 'type-check "argument type does not match parameter type: ~a += ~a" T-rand S)
            (values T (multiset-add-all FV-rator FV-rand)))]
       [else
        (error 'type-check "in application, expected a function, not ~a" T-rator)
        ])]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Testing

(define P0 `(un 42))
(check-equal? (run P0) 42 "Program P0 should return 42")

(define P1 `((un (lambda (x : (un int)) x)) (un 42)))
(check-equal? (run P1) 42 "Program P1 should return 42")

(define P2 `((lin (lambda (x : (lin int)) x)) (lin 42)))
(check-equal? (run P2) 42 "Program P2 should return 42")

(define P3 `(if (un #t) (un 42) (un 0)))
(check-equal? (run P3) 42 "Program P3 should return 42")

(define P4 `(if (lin #t) (lin 42) (lin 0)))
(check-equal? (run P4) 42 "Program P4 should return 42")

(define P5 `(lin (+ (lin 40) (lin 2))))
(check-equal? (run P5) 42 "Program P5 should return 42")

(define P6 '((lin (lambda (x : (lin int)) (lin (+ x x)))) (lin 21)))
(with-handlers ([exn:fail? (lambda (exn) (void))])
               (run P6)
               (check-true #f))

(define P7 '((lin (lambda (x : (un int)) (un (+ x x)))) (un 21)))
(check-equal? (run P7) 42 "Program P7 should return 42")


(define P8 '(split (lin (pair (lin 40) (lin 2))) (x y) (lin (+ x y))))
(check-equal? (run P8) 42 "Program P8 should return 42")

(define P9 '(split (dup ((frac 1) 21)) (x y) (lin (+ x y))))
(check-equal? (run P9) 42 "Program P9 should return 42")

(define P10 '((lin (lambda (x : (frac int)) (lin (+ x x)))) (lin 21)))
(with-handlers ([exn:fail? (lambda (exn) (void))])
               (run P10)
               (check-true #f))


