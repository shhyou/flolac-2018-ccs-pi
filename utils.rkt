#lang racket/base

(provide run-many)

(require racket/match
         racket/pretty
         redex/reduction-semantics)

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
