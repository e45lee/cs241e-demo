#lang racket
(define (dne dn) (call/cc (lambda (cont) (dn cont))))
(define (dn neg) (neg "hello"))

(dne dn)
