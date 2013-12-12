#lang racket

;;(require "pkputils.rkt")
(require test-engine/racket-tests)

(provide (all-defined-out))

;; average: (listof number) -> number
(define (average l)
  (/ (foldl + 0.0 l) (length l)))

(define N-PLACES 2)
;; my-round: number -> number
;; round to N-PLACES
(define (my-round n) (/ (round (* n (expt 10 N-PLACES))) (expt 10 N-PLACES)))

;; outputify: (listof number) -> string
;; format for cut/paste into R
(define (outputify lon)
  (foldr (lambda (n res) (string-append (number->string (my-round n)) "," res))
         ""
         lon))
  
(define HISTO-BINS 100)
;; histogramify: (listof number) number -> (vectorof number)
;; create the histogram over n-buckets from the list of numbers (numbers assumed [0,1])
(define (histogramify lon (n-buckets HISTO-BINS))
  (local ((define v (make-vector (add1 n-buckets)))
          ;; indexify: number -> N
          ;; determine the appropriate index for the given number
          (define (indexify num)
            (inexact->exact (floor (* num n-buckets))))
          )
    (for-each (lambda (n) (vector-set! v (indexify n) (add1 (vector-ref v (indexify n)))))
              lon)
    v))
            


#|
NAIVE AND ASTUTE VOTER MODEL

Voters have a bias toward one of two candidates.  

Naive voters start with a 0.5 bias.  Based on interactions with subsets of users, they may adjust their bias.

Astute voters always vote for the good candidate and never change their bias based on interactions.

ToDo:
* representation of voter
* random partitioning of population
* bias update of voters within partition
* do the random partitioning and bias update some number of times
* determine vote outcome
* gather results
* add astute voters

|#

(define VOTE-TIMES 1) ;; for given population of voter-biases, determine likely vote outcome

(struct voter (type bias) #:mutable)
;; a voter is an interface:
;; 1. 'type :: symbol
;; 2. 'bias :: number
;; 3. 'update :: (number number -> (void) )
;; 4. 'vote :: number

;; make-voter: symbol number -> voter
;; create a voter
(define (make-voter type0 bias0)
  (local ((define bias bias0)
          
          ;; vote:  -> number
          ;; probabilistically vote according to current bias value
          ;; unless astute voter, in which case always vote 1
          (define (vote)
            (cond [(symbol=? type0 'naive)
                   (if (< (random) bias) 1 0)]
                  [else 1]))
          
          ;; update-bias: number number -> void
          ;; given a collective voting outcome in range [0,1] and this voter's recent vote,
          ;; update this voter's bias toward the group-think
          ;; unless astute voter, in which case don't bother
          (define (update-bias vote gt)
            (unless (symbol=? type0 'astute)
              (local ((define group-tilt (sgn (- gt 0.5)))
                      ;;(define vote-alignment (* group-tilt (sgn (- 0.5 vote))))
                      (define willingness-to-change (- 0.25 (sqr (- bias 0.5))))
                      )
                (set! bias (abs (+ bias (* (+ 0.4 (/ (random) 5)) ;; random learning-rate
                                           group-tilt willingness-to-change))))
                #|
(cond [(> bias 1.0) (set! bias 1.0)]
                      [(< bias 0.0) (set! bias 0.0)]
                      [else 'do-nothing])
                |#
                (unless (<= 0.0 bias 1.0)
                  (printf "Large bias in update-bias ~a~%" bias)))))
          
          ;; service-manager: symbol -> ...
          (define (service-manager msg)
            (cond [(symbol=? msg 'type) type0]
                  [(symbol=? msg 'bias) bias]
                  [(symbol=? msg 'update) update-bias]
                  [(symbol=? msg 'vote) (vote)]
                  [else (error 'voter-class "unrecognized message")])))
    service-manager))
          

;; make-naive-vpop: N -> (listof voter)
;; create a list of n naive voters
(check-within (map (lambda (v) (v 'bias)) (make-naive-vpop 10))
              (build-list 10 (lambda (_) 0.5)) 0.01)
(define (make-naive-vpop n)
  (make-vpop n 'naive 0.5))

;; make-vpop: N symbol -> (listof voter)
;; create list of n voters of the given type
(check-within (map (lambda (v) (v 'bias)) (make-vpop 10 'any 0.3))
              (build-list 10 (lambda (_) 0.3)) 0.01)
(define (make-vpop n type bias)
  (build-list n (lambda (_) (make-voter type bias))))

;; make-mixed-vpop: N N -> (listof voter)
;; create list of n naive voters and a astute voters
(define (make-mixed-vpop n a)
  (append (make-vpop a 'astute 1.0)
          (make-naive-vpop n)))

;; shuffle-pop: (listof voter) -> (listof-voter)
;; using the Fisher-Yates shuffle algorithm
(define (shuffle-pop lov)
  (local ((define pv (list->vector lov))
          (define (swap i j)
            (let ((tmp (vector-ref pv i)))
              (vector-set! pv i (vector-ref pv j))
              (vector-set! pv j tmp)))
          (define (fisher-yates i)
            (cond [(zero? i) (void)]
                  [else
                   (swap (random i) i)
                   (fisher-yates (sub1 i))]))
          )
    (fisher-yates (sub1 (vector-length pv)))
    (vector->list pv)))

;; partition-voters: (listof voter) N -> (listof (listof voter))
;; randomly partition the population into groups of size n
(define (partition-voters lov n)
  (unless (zero? (modulo (length lov) n)) (error 'partition-voters "invalid attempted grouping"))
  (local ((define (pvhelp l)
            (cond [(empty? l) empty]
                  [else (cons (take l n)
                              (pvhelp (drop l n)))])))
    (pvhelp (shuffle-pop lov))))

;;--- adjust biases


;; update-biases: (listof voter) -> (void)
;; within a group of voters, each reports their intended vote, and then updates! their respective biases
;; based on the collective intentions
(define (update-biases lov)
  (local ((define votes (map (lambda (v) (v 'vote)) lov))
          (define group-think (average votes)))
    #|
    (printf "group think: ~a from votes ~a~n" 
            group-think
            (foldr (lambda (voter vote result) 
                     (string-append (format " ~a: ~a, " (voter-bias voter) vote) result))
                   "" lov votes))
    |#
    (for-each (lambda (voter this-vote) ((voter 'update) this-vote group-think)) lov votes)))

;;--- do the stuff

;; caucus: (listof voter) N N -> (listof voter)
;; for some n-times of iterations, partition the population into group-size and update within those groups
(define (caucus lov n-times group-size)
  (local ((define (ch i)
            (cond [(zero? i) (void)]
                  [else (for-each update-biases (partition-voters lov group-size))
                        (ch (sub1 i))])))
    (ch n-times)
    lov))

;; n-vote-outcomes: (listof voter) N -> number
;; determine the outcome of the probabilistic votes of the given voters, repeated and averaged over n times
(define (n-vote-outcomes lov n)
  (/ (foldl + 0.0 (build-list n (lambda (_) (vote-outcome lov))))
     n))

;; vote-outcome: (listof voter) -> number
;; determine the outcome for a single vote of the population
(define (vote-outcome lov)
  (/ (foldl + 0.0 (map (lambda (v) (v 'vote)) lov)) (length lov)))

;; exp0: (listof voter) N N -> number
;; for population,  caucus-iterations, and group-size, find the final outcome of the vote
(define (exp0 pop caucus-times group-size)
    (caucus pop caucus-times group-size)
    (n-vote-outcomes pop VOTE-TIMES))
  
;; exp1: N N N -> number
;; for population-size, caucus-iterations, and group-size, find the final outcome of the vote
(define (exp1 pop-size caucus-times group-size)
  (exp0 (make-naive-vpop pop-size) caucus-times group-size))

;; exp2: N N N N -> number
;; for pop-size, of which there are astutes voters, caucus-times and group-size, find final outcome of the vote
(define (exp2 pop-size astutes caucus-times group-size)
  (exp0 (make-mixed-vpop (- pop-size astutes) astutes) caucus-times group-size))

;;(test)

;; empirical-vote-outcome: N N N -> number
;; perform how-many samples of votes among total voters, with astute voters voting 'for', and remainder undecided
(define (empirical-vote-outcome how-many total astute)
  (do ([i 0 (add1 i)]
       [sum 0.0 (+ sum 
                 (if (> (n-vote-outcomes (make-mixed-vpop (- total astute) astute) 1) 0.5)
                     1 0))])
    ((>= i how-many) (/ sum how-many))))

;; bias-drift: (listof (listof voter)) number
;; gather the average bias drift over a collection of populations as a result of caucusing.
;; note: caucusing mutates the voters in a population, so we can return the average distribution.
(define (bias-drift lopops caucustimes caucussize)
  (if (< caucustimes 0)
      empty
      (let ((adist (merge-bias-distribution lopops)))
        (for-each (lambda (p) (caucus p 1 caucussize)) lopops)
        (cons adist (bias-drift lopops (sub1 caucustimes) caucussize)))))

;; merge-bias-distribution: (listof (listof voter)) -> (listof probability)
;; given a collection of populations, merge their bias distributions into a single histogram
(define (merge-bias-distribution lopops)
  (vector->list
   (vector-map! (lambda (c) (/ c (length lopops)))
                (foldl (lambda (hist res)
                         (vector-map! (lambda (x y) (+ x y))
                                      res hist))
                       (make-vector (add1 HISTO-BINS))
                       (map (lambda (pop) (histogramify (map (lambda (v) (v 'bias)) pop)))
                            lopops)))))

(test)