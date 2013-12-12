#lang racket

(require "influence.rkt")
(require test-engine/racket-tests)
(require plot)
(require plot/utils)

(provide (all-defined-out))

;; THEORETICAL MODELS

;; NAIVE- AND ASTUTE-VOTER MODELS

;; enough-undecided?: number number number -> boolean
;; returns true if there exists at least one voting scenario (all u vote yes) for win
(check-expect (enough-undecided? 1 5 4) false)
(check-expect (enough-undecided? 1 5 5) true)
(check-expect (enough-undecided? 3 3 3) true)
(define (enough-undecided? y n u)
  (>= u (+ (- n y) 1)))

;; min-undecided-yes: number number number -> number
;; compute the minimum number of undecideds that can vote yes and still have yes win
(check-expect (min-undecided-yes 6 8 5) 4)
(check-expect (min-undecided-yes 6 7 5) 4)
(check-expect (min-undecided-yes 5 1 3) 0)
(check-expect (min-undecided-yes 3 3 3) 2)
(check-expect (min-undecided-yes 3 2 3) 2)
(check-expect (min-undecided-yes 3 1 3) 1)
(check-expect (min-undecided-yes 1 3 3) 3)
(define (min-undecided-yes y n u)
  (+ (floor (/ (+ n (- y) u) 2)) 1))

;; num-terms: number number number -> number
;; compute the number of terms in the sum of valid numbers of undecideds voting yes
(check-expect (num-terms 6 8 5) 2)
(check-expect (num-terms 3 2 3) 2)
(check-expect (num-terms 3 1 3) 3)
(check-expect (num-terms 5 1 3) 4)
(define (num-terms y n u)
  (+ (- u (min-undecided-yes y n u)) 1))

;; p-win: number number number -> probability
;; for committed for and against and undecided, what is probability that yes wins the vote
(define (p-win for against undecided)
  (if (enough-undecided? for against undecided)
      (let* ((total (+ for against undecided))
         (half-maybe-plus (+ (floor (/ total 2)) 1)))
    (foldl + 0.0
    ;;(map (lambda (n) n)
           (build-list (num-terms for against undecided)
                       (lambda (nuf) ;; for each possible number of undecideds voting 'for'
                         (/ (binomial undecided 
                                      (+ nuf (min-undecided-yes for against undecided)))
                            (expt 2 undecided))))))
      0))

;; contribution-a-of-n : number number -> probability
;; compared to a population of n naive voters, compute the contribution of a astute voters
(define (contribution-a-of-n a n)
  (- (p-win a 0 (- n a))
     (p-win 0 0 n)))


;; BASIC UTILITIES: THEORETICAL MODEL OF VOTING


;; decide-share: number number -> number
;; compute the share of a 'deciding winning vote' that each voter gets for voting 'for'
;; based on number of votes needed to win (i.e., one more than those voting against) divided by voters 'for'
(check-expect (decide-share 3 2) 1)
(check-expect (decide-share 11 7) 5/7)
(define (decide-share total for)
  (if (>= (- total for) for)
      0
      (/ (+ (- total for) 1) 
         for)))


(define (fact n)
  (if (zero? n)
      1
      (* n (fact (sub1 n)))))

;; binomial: number number -> number
;; compute binomial coefficient 
(check-expect (binomial 11 10) 11)
(check-expect (binomial 11 1) 11)
(check-expect (binomial 5 3) 10)
(check-expect (binomial 5 2) 10)
(define (binomial n k) (binomial-b n k))
(define (binomial-a n k)
  (local ((define (compute-it n k)
            (foldl * 1 
                   (map / 
                        (build-list (- n k) (lambda (i) (+ i k 1)))
                        (build-list (- n k) (lambda (i) (+ i 1)))))))
    (if (> k (/ n 2))
        (compute-it n k)
        (compute-it n (- n k)))))

(define (binomial-b n k)
  (local ((define (compute-it n k)
            (/ (for/product ([p (in-range (add1 k) (add1 n))]) p)
               (for/product ([p (in-range 1 (add1 (- n k)))]) p))))
    (if (> k (/ n 2))
        (compute-it n k)
        (compute-it n (- n k)))))

;; prob-outcome: number number -> number
;; compute the probability of a particular outcome with total voters and winning voting for the winning side
(check-expect (prob-outcome 5 3) (/ 10 32))
(define (prob-outcome total winning)
  (/ (binomial total winning)
     (expt 2 total)))


;; expected-share: number number -> number
;; the expected share in a given outcome given the probability of that outcome
(check-expect (expected-share 5 4) (* 5/32 1/2))
(define (expected-share total winning)
  (* (prob-outcome total winning)
     (decide-share total winning)))

;; ADD UNDECIDEDS TO MODEL
;; where undecided voters flip an even coin to vote one way or the other

;; one-outcome-expect-share-w/-undecided: number number number number -> number
;; compute probability of a particular vote (total, for) 
;; CONDITIONED ON (tot-for minus nuf) are voting 'for' and that nuf of undecided (both included in total and tot-for) vote 'for'
(check-expect (one-outcome-expect-share-w/-undecided 5 3 4 2) (* (prob-outcome 4 2) (decide-share 5 3)))
(check-expect (one-outcome-expect-share-w/-undecided 11 6 0 0) (decide-share 11 6))
(check-expect (one-outcome-expect-share-w/-undecided 11 5 1 0) 0)
(check-expect (one-outcome-expect-share-w/-undecided 11 6 1 1) (* (prob-outcome 1 1) (decide-share 11 6)))
(check-expect (one-outcome-expect-share-w/-undecided 10 5 0 0) 0)
(check-expect (one-outcome-expect-share-w/-undecided 10 6 0 0) (decide-share 10 6))
(check-expect (one-outcome-expect-share-w/-undecided 10 6 1 1) (* (prob-outcome 1 1) (decide-share 10 6)))
(define (one-outcome-expect-share-w/-undecided total tot-for undec nuf)
  (* 
   ;; probability that nuf undecided voters vote 'for'
   (/ (binomial undec nuf) ;; undecided choose nuf
      (expt 2 undec))      ;; divided all possible undecided votes
   ;; everyone's share in such a vote (tot-for that includes nuf)
   (decide-share total tot-for)))
  

;; expect-shr-w-undecideds: number number number -> number
;; compute expected share of decisive vote with fixed for and against, and some undecideds who could vote either way
(check-expect (expect-shr-w-undecideds 5 5 1) (* (prob-outcome 1 1) (decide-share 11 6)))
(define (expect-shr-w-undecideds for against undecided)
  (let* ((total (+ for against undecided))
         (half-maybe-plus (+ (floor (/ total 2)) 1)))
    ;(printf "total : ~a~%half-maybe-plus : ~a~%" total half-maybe-plus)
    (foldl + 0
           (build-list (add1 undecided)
                       (lambda (nuf) 
                         (one-outcome-expect-share-w/-undecided total (+ for nuf) undecided nuf))))))

;; probability-win: number number number -> number
;; compute the simple probability of a winning ('for') vote outcome when
;; given a number of voters for, against, and undecided, where undecideds flip an even coin 
(define (probability-win for against undecided)
  (let* ((total (+ for against undecided))
         (half-maybe-plus (+ (floor (/ total 2)) 1)))
    (foldl + 0.0
           (build-list (add1 undecided) 
                       (lambda (nuf) ;; for each possible number of undecideds voting 'for'
                         (if (> (+ for nuf) (+ against (- undecided nuf)))
                             (/ (binomial undecided (abs (- undecided nuf)))
                                (expt 2 undecided))
                             0))))))

(plot (list (function (lambda (p) (probability-win (* 100 p) (- 90 (* 100 p)) 10)) 2/5 3/5 #:samples 11)
            (function (lambda (p) (probability-win (* 1000 p) (- 900 (* 1000 p)) 100)) 2/5 3/5 #:samples 101)
            ;(function (lambda (n) (probability-win n (- 9000 n) 1000)) 4500 5500 #:samples 1001)
            )
      #:y-min 0 #:y-max 1)

;; win-contrib: number number number -> number
;; attempt to convince Tom Knecht of a better model
;; compute the difference in probability of win given for, against, and undecided voters,
;; where one undecided becomes astute and decides to vote 'for' 
(define (win-contrib for against undecided)
  (- (probability-win (add1 for) against (sub1 undecided))
     (probability-win for against undecided)))


;; PLOTTING FIGURES

;; plot-histogram : (listof number) [string] -> image
;; generate plot of given distribution, possibly writing to file when optional arg present
(define (plot-histogram histo (ofile #f))
  (plot (list (lines (map (lambda (bin bincount) (vector (/ bin HISTO-BINS) bincount))
                          (build-list (length histo) (lambda (n) n))
                          histo)
                     #:color 'green))
        #:out-file ofile
        #:x-min 0 #:x-max 1.0
        #:y-min 0 #:y-max (foldl + 0 histo)
        #:x-label "voter bias"
        #:y-label "frequency"
        ))

;; plot-bias-distribution: (listof voter) -> image
;; given a population, plot the frequency distribution of the voters' biases
(define (plot-bias-distribution pop (ofile #f))
  (plot-histogram (vector->list (histogramify (map (lambda (v) (v 'bias)) pop) 100)) ofile))


(plot (list (function (lambda (n)
                        (let* ((for (inexact->exact (round (* n .43))))
                               (undec (inexact->exact (round (* n .1))))
                               (against (- n for undec)))
                          (win-contrib for against undec))) 10 500 #:samples 51 #:color 'blue)
            (function (lambda (n)
                        (let* ((for (inexact->exact (round (* n .43))))
                               (undec (inexact->exact (round (* n .1))))
                               (against (- n for undec)))
                          (expect-shr-w-undecideds for against undec))) 10 500 #:samples 51))
      #:y-min 0 #:y-max 1)

(plot (list (lines (build-list 50 (lambda (n)
                                    (let* ((for (round (* n 46/100)))
                                           (undec (round (* n 8/100)))
                                           (against (- n for undec)))
                                      (vector n (win-contrib for against undec)))))
                   #:color 'blue)
            (lines (build-list 50 (lambda (n)
                                    (let* ((for (round (* n 46/100)))
                                           (undec (round (* n 8/100)))
                                           (against (- n for undec)))
                                      (vector n (expect-shr-w-undecideds for against undec)))))
                   #:color 'green))
      #:x-label "number of voters"
      #:y-label "gain-from-voting | contribution-share")


;; plot a comparison of theoretical (blue) and empirical (green) probability of favorable outcomes
;; for different proportions of astute voters (from 0% or 0.01% to 10%)
#|
(plot (list (lines (for/list ([astute '(0 1 5 10 20 40 70 100 200 300 1000)]
                              )
                     (vector (/ astute 10000.0) (probability-win astute 0 (- 10000 astute))))
                   #:color 'blue)
            (lines (for/list ([astute '(0 1 5 10 20 40 70 100 200 300 1000)]
                              )
                     (vector (/ astute 10000.0) (empirical-vote-outcome 1000 10000 astute)))
                   #:color 'green))
      #:x-label "proportion of astute voters"
      #:y-label "proportion of favorable outcomes"
      #:y-min 0.0
      #:y-max 1.0
      #:x-min 0.0
      #:x-max 0.1
      )
|#                   

                

;; MAKE PLOTS

;; graph-three: number -> image
;; for a total number of voters, generate a graph with three lines,
;; one for share of deciding vote, probability of given vote outcome, and expected influence
(define (graph-three total)
  (let ((mid (/ (+ total 1) 2)))
    (plot (list (function (lambda (n) (decide-share total n)) mid total #:y-min 0 #:y-max 1 
                          #:samples mid #:color 0 #:label "share of deciding vote")
                (function (lambda (n) (prob-outcome total n)) mid total #:y-min 0 #:y-max 1 
                          #:samples mid #:label "prob. outcome")
                (function (lambda (n) (expected-share total n)) mid total #:y-min 0 #:y-max 1 
                          #:samples mid #:color 5 #:label "expected influence"))
          #:x-label "number of winning voters"
          #:y-label "share or probability"
          )))

;; USING: probability-win and empirical-vote-outcome

;; Population 100, re-run: 0,1,2,4,8,16,32 astutes; blue-theory; green-sim(10K): 
(plot (list #|(lines (list (vector 0 0.4469)
                           (vector 1 0.4958)
                           (vector 2 0.5376)
                           (vector 4 0.6211)
                           (vector 8 0.7682)
                           (vector 16 0.9498)
                           (vector 32 1.0))
                   #:color 'green)|#
       (lines (list (vector 0 0.477)
                    (vector 1 0.511)
                    (vector 2 0.517)
                    (vector 4 0.626)
                    (vector 8 0.781)
                    (vector 16 0.943)
                    (vector 32 0.999))
              #:color 'green)
       (lines (list (vector 0 0.46020538130641064)
                    (vector 1 0.4999999999999998)
                    (vector 2 0.5401965845389792)
                    (vector 4 0.6201753558381852)
                    (vector 8 0.7671462771134688)
                    (vector 16 0.9494318289305974)
                    (vector 32 0.9999345806192291))
              #:color 'blue)
       )
      #:x-min 0.0 #:y-min 0.4
      #:x-max 40 #:y-max 1.0
      #:x-label "number of astute voters (of 100)" #:y-label "probability of win")
      
;; pop 1000, 1000simrep
(plot (list (lines (list (vector 0 0.489)
                         (vector 1 0.518)
                         (vector 2 0.509)
                         (vector 4 0.555)
                         (vector 8 0.565)
                         (vector 16 0.683)
                         (vector 32 0.833))
                   #:color 'green)
            ;; other empirical run
            (lines (list (vector 0 0.475)
                         (vector 1 0.493)
                         (vector 2 0.496)
                         (vector 4 0.511)
                         (vector 8 0.598)
                         (vector 16 0.683)
                         (vector 32 0.843))
                   #:color 'red)
            (lines (list (vector 0 0.4873874909108196)
                         (vector 1 0.49999999999999994)
                         (vector 2 0.512625134223404)
                         (vector 4 0.5378627395466173)
                         (vector 8 0.5879335318314977)
                         (vector 16 0.6837287171426142)
                         (vector 32 0.8404664983742928))
                   #:color 'blue))
      ;; #:out-file "modelsim1K.jpg"
      #:x-min 0.0 #:y-min 0.4
      #:x-max 40 #:y-max 1.0
      #:x-label "number of astute voters (of 1000)" #:y-label "probability of win")
      
            

;; pop 10,000; 1000 simrep
(plot (list (lines (list (vector 0 0.489)
                         (vector 1 0.525)
                         (vector 2 0.496)
                         (vector 4 0.518)
                         (vector 8 0.513)
                         (vector 16 0.559)
                         (vector 32 0.634))
                   #:color 'green)
            (lines (list (vector 0 0.4960106769303089)
                         (vector 1 0.5)
                         (vector 2 0.5039897220418951)
                         (vector 4 0.5119687670337537)
                         (vector 8 0.5279140885911324)
                         (vector 16 0.5596646031357814)
                         (vector 32 0.6219076615128083))
                   #:color 'blue))
      ;; #:out-file "modelsim10K.jpg"
      #:x-min 0.0 #:y-min 0.4
      #:x-max 40 #:y-max 1.0
      #:x-label "number of astute voters (of 10,000)" #:y-label "probability of win")
      

(test)