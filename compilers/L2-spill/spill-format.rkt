#lang racket

(require racket/cmdline)

(define file-to-compile
  (command-line
   #:args (filename)
   filename))

(define in (open-input-file file-to-compile))

(define func (read in))
(define var (read in))
(define prefix (read in))

(displayln func)
(displayln var)
(displayln prefix)