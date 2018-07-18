#lang racket/base

(provide run-many
         set-remove
         set-subtract)

(require racket/match
         racket/pretty
         redex/reduction-semantics)

(define-language lang-empty
  [x ::= variable-not-otherwise-mentioned])

(define-metafunction lang-empty
  set-remove : (x ...) x -> (x ...)
  [(set-remove () x) ()]
  [(set-remove (x_1 ...) x_2)
   (x_remain ...)
   (where/error (x_remain ...)
                ,(for/list ([x (in-list (term (x_1 ...)))]
                            #:unless (equal? x (term x_2)))
                   x))])

(define-metafunction lang-empty
  set-subtract : (x ...) (x ...) -> (x ...)
  [(set-subtract (x ...) ())             (x ...)]
  [(set-subtract (x ...) (x_1 x_2 ...))  (set-subtract (set-remove (x ...) x_1)
                                                       (x_2 ...))])

(define (run-many fuel R t
                  #:verbose? [verbose? #f]
                  #:use-fuel [consume-fuel sub1]
                  #:compare [compare-rule-name string<?])
  (parameterize ([pretty-print-columns 50])
    (pretty-write t))
  (define next-steps
    (sort (apply-reduction-relation/tag-with-names R t)
          compare-rule-name
          #:key car))
  (cond
    [(< fuel 0)
     (when verbose? (printf "\nRun out of fuel.\n"))
     t]
    [(null? next-steps) t]
    [else
     (match-define (cons (list rule-name t-next) _) next-steps)
     (when verbose? (printf "\n============ ~s ============\n\n" rule-name))
     (run-many (consume-fuel (car next-steps) fuel)
               R
               t-next
               #:verbose? verbose?
               #:use-fuel consume-fuel
               #:compare compare-rule-name)]))
