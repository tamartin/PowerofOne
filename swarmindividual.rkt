#lang racket
(require lang/posn)
(require 2htdp/universe)
(require 2htdp/image)

;; 1. Critter interface and objects
;; 2. Critter types and species-selective swarming
;; 3. Efficiency

;; Swarming: Deliverable 4

;; DEFINITIONS

(define WIDTH 800)
(define HEIGHT 600)
(define DELAY 0.03)
(define 2PI (* 2 pi))
(define PI/2 (/ pi 2))

;; critter: is an interface
;; 1. 'draw-on :: (image -> image)
;; 3. 'update-vel :: (swarm -> true)
;; 4. 'move :: critter
;; 5. 'loc :: posn
;; 6. 'vel :: posn
;; 7. 'type :: symbol
;;---------- (other services)
;; 'set-vel! :: (posn -> void)
;; 'report-kills :: number
;; 'reset-kills :: (void)
;; 'killed-respawn :: (void)
;; 'killed? :: boolean


;; a param-vec is a vector:
;; (vector number number number number number number number number number number)
(define default-param-vec
  (vector 3 ;; CRITTER-RADIUS
	  15 ;; CRITTER-POINTER
	  40 ;; NEIGHBOR-RADIUS
	  (* pi 0.75) ;; FIELD-OF-VIEW
	  0.9 ;; ALIGNMENT-W
	  0.9 ;; COHESION-W
	  1.1 ;; SEPARATION-W
	  1.7 ;; EDGE-W
	  0.8 ;; NOMINAL-SPEED-W
          1.3 ;; AVOID-OTHER-TYPE-W
	  ))
(define type-a        (vector 3 8 35  (* pi 0.75) 1.9 1.5 1.4 3.0 0.8 1.8))
(define type-b        (vector 6 11 50 (* pi 0.75) 0.9 1.1 1.2 1.7 0.8 0.8))
(define type-c        (vector 4 9 25  (* pi 0.75) 0.9 0.9 1.1 1.7 0.8 0.3))
(define t-wolf        (vector 3 20 65 (* pi 0.55) 0.3 0.3 1.5 3.0 0.5 -1.5))
(define t-sheep       (vector 5 15 50 (* pi 0.97) 1.0 1.15 1.05 3.0 0.6 2.1))
(define t-sheep-scout (vector 5 15 99 (* pi 0.97) 1.0 1.15 1.05 3.0 0.6 2.1)) ;; differ only in neighbor-radius

;; a swarm is a (listof critter)

;; UTILITIES

;; v-mag: posn -> number
;; compute the magnitude of the vector represented as a posn
(define (v-mag v)
  (sqrt (+ (sqr (posn-x v)) (sqr (posn-y v)))))

;; v-mag2: posn -> number
;; compute the magnitude SQUARED of the vector represented as a posn
(define (v-mag2 v)
  (+ (sqr (posn-x v)) (sqr (posn-y v))))

;; v+ : posn posn -> posn
;; computer the vector sum of two posn
(define (v+ p1 p2)
  (make-posn (+ (posn-x p1) (posn-x p2))
	     (+ (posn-y p1) (posn-y p2))))

;; v- : posn posn -> posn
;; compute the vector displacement of two vectors (posns)
(define (v- p1 p2)
  (make-posn (- (posn-x p1) (posn-x p2))
	     (- (posn-y p1) (posn-y p2))))

;; v-scale : number posn -> posn
;; scalar product that alters the length of a given vector (posn)
(define (v-scale n p)
  (make-posn (* n (posn-x p)) (* n (posn-y p))))

;; v-norm : posn -> posn
;; normalize a vector so it has unit magnitude
;; UNLESS it is a 0-length vector -- then leave it
(define (v-norm p)
  (if (v-zero? p) 
      p
      (v-scale (/ 1 (v-mag p)) p)))

;; v-dot-prod : posn posn -> number
;; compute the dot-product of two vectors
(define (v-dot-prod p1 p2)
  (+ (* (posn-x p1) (posn-x p2)) (* (posn-y p1) (posn-y p2))))

;; v-mod! : posn -> posn
;; wrap a posn that might have fallen off the edge
(define (v-mod! p)
  (begin (set-posn-x! p (modulo (round (posn-x p)) WIDTH))
         (set-posn-y! p (modulo (round (posn-y p)) HEIGHT))
         p))

;; v-zero? : posn -> boolean
;; determine if the given vector is zero-length
(define (v-zero? p)
  (and (zero? (posn-x p)) (zero? (posn-y p))))


;; CRITTER CLASS (INTERFACE)

;; make-critter: param-vec posn posn symbol symbol number -> critter
;; critter constructor
(define (make-critter pvec loc0 vel0 type0 color0 def-speed0)
  (local
   (
    (define CRITTER-RADIUS (vector-ref pvec 0))
    (define CRITTER-POINTER (vector-ref pvec 1))
    (define CRITTER-COLOR color0)
    (define CRITTER-IMAGE (rotate -90 (isosceles-triangle CRITTER-POINTER 20 'solid color0)))
    (define NEIGHBOR-RADIUS (vector-ref pvec 2))
    (define NEIGHBOR-RADIUS-SQUARED (sqr NEIGHBOR-RADIUS))
    (define FIELD-OF-VIEW (vector-ref pvec 3))
    (define COS-FIELD-OF-VIEW (cos FIELD-OF-VIEW))
    (define KILL-ZONE 16)
    (define FEEDING-TIME (* 10 CRITTER-RADIUS))
    ;; steering vector weights
    (define ALIGNMENT-W (vector-ref pvec 4))
    (define COHESION-W (vector-ref pvec 5))
    (define SEPARATION-W (vector-ref pvec 6))
    (define EDGE-W (vector-ref pvec 7))
    (define NOMINAL-SPEED-W (vector-ref pvec 8))
    (define AVOID-OTHER-TYPE-W (vector-ref pvec 9))
    ;; internal critter structure definition
    (define loc loc0)
    (define new-loc loc0)
    (define vel vel0)
    (define new-vel vel0)
    (define type type0)
    (define nom-speed def-speed0)
    ;; persistent edge-posns for computing edge-avoidance
    (define ww (make-posn 0 0))
    (define wn (make-posn 0 0))
    (define we (make-posn WIDTH 0))
    (define ws (make-posn 0 HEIGHT))
    (define mini-posn-swarm (list ww wn we ws))
    ;; managing kills and killed
    (define n-kills 0)
    ;;(struct bloodspot (loc size) #:mutable)
    ;;(define blood-spots empty)
    (define killed-respawn #f)
    (define feeding 0)

    ;; DRAWING

    ;; display-critter: image -> image
    ;; generate the triangle image at the current heading for this critter
    (define (display-critter i)
      (place-image (rotate 
                    (* -360 (/ (atan (posn-y vel) (posn-x vel)) 2PI))
                    CRITTER-IMAGE)
                   (posn-x loc) (posn-y loc) 
                   (if (positive? feeding)
                       (place-image (circle feeding 'solid 'red)
                                    (posn-x loc) (posn-y loc) i)
                       i)))
    
    ;; NEIGHBORHOODS

    ;; neighbor-posn?: posn -> boolean
    ;; determine if the posn (already known to be close-enough) is a neighbor
    (define (neighbor-posn? p)
      (and (not (equal? loc p))
	   (in-fov? p)))

    ;; near? : posn -> boolean
    ;; determine if a posn is near me depending on NEIGHBOR-RADIUS
    (define (near? p2)
      (<= (v-mag2 (v- loc p2)) NEIGHBOR-RADIUS-SQUARED))

    ;; in-fov? : posn -> boolean
    ;; determine if the posn is within my field of view
    (define (in-fov? p2)
      (> (cosine-angle-between p2)
	 COS-FIELD-OF-VIEW))

    ;; cosine-angle-between: posn -> number
    ;; determine the angular deviation between a critter's current heading and a given point
    (define (cosine-angle-between a-point) 
      (/ (v-dot-prod vel
		     (v- a-point loc))
         (* (v-mag vel) (v-mag (v- a-point loc)))))

    ;; get-my-neighbors : swarm -> swarm
    ;; return the critters from the swarm that are near and like me
    (define (get-my-neighbors s)
      (filter (lambda (x) (and (symbol=? type (x 'type))
                               (neighbor-posn? (x 'loc))))
	      s))
    
    ;; get-others-close : swarm -> swarm
    ;; return the critters from the swarm that are close but not like me
    (define (get-others-close s)
      (let ((others (filter (lambda (x) (and (not (symbol=? type (x 'type)))
                                             (neighbor-posn? (x 'loc))))
                            s)))
        ;; check for kills if this is a wolf
        (when (symbol=? type 'wolf)
          (for-each (lambda (c)
                      (when (< (v-mag2 (v- loc (c 'loc))) KILL-ZONE)
                        (set! n-kills (add1 n-kills))
                        (set! feeding FEEDING-TIME)
                        ;;(printf "kill with dist: ~a, loc: ~a, and prey: ~a~%" (v-mag2 (v- loc (c 'loc))) loc (c 'loc))
                        (c 'killed-respawn)
                        )) others))
        others))

    ;; STEERING

    ;;--- Separation behaviors ---

    ;; get-separation-vector: swarm -> number
    ;; compute the appropriate steering vector for me to acheive separation
    (define (get-separation-vector s)
      (foldr (lambda (cx p) (v+ (get-repulsion-vector (cx 'loc)) p))
	     (make-posn 0 0)
             s))

    ;; get-repulsion-vec : posn -> posn
    ;; compute the weighted vector from the posn in the direction of myself
    (define (get-repulsion-vector p2)
      (v-scale (/ 1 (v-mag2 (v- loc p2)))
	       (v- loc p2)))

    ;;--- Cohesion behaviors ---

    ;; get-cohesion-vector: swarm -> number
    ;; compute appropriate turn maneuver for given critter to stay close to its neighbors
    (define (get-cohesion-vector s)
      (cond [(empty? s) (make-posn 0 0)]
	    [else 
	     (v- (v-scale (/ 1 (length s))
			  (foldr (lambda (c accum) (v+ (c 'loc) accum))
				 (make-posn 0 0)
				 s))
		 loc)]))

    ;;--- Alignment behaviors ---

    ;; avg-veloc: swarm -> number
    ;; find the average velocity for all critters in NON-EMPTY swarm
    (define (avg-veloc s)
      (cond [(empty? s) (make-posn 0 0)]
            [else
             (v-scale (/ 1 (length s))
                      (foldr (lambda (c accum) (v+ (c 'vel) accum))
                             (make-posn 0 0)
                             s))]))
      
    ;; get-alignment-vector: swarm -> posn
    ;; compute the appropriate velocity adjustment to align the critter with its neighbors
    (define (get-alignment-vector s)
      (cond [(empty? s) (make-posn 0 0)]
	    [else (v- (avg-veloc s) vel)]))
      
    ;;--- Edge avoidance behaviors ---

    ;; get-edge-vector:  -> posn
    ;; compute the appropriate anti-edge vector for my current position
    (define (get-edge-vector)
      (local ((define edge-neighbors empty))
        (begin
          (set-posn-y! ww (posn-y loc))
          (set-posn-x! wn (posn-x loc))
          (set-posn-y! we (posn-y loc))
          (set-posn-x! ws (posn-x loc))
          (set! edge-neighbors (filter (lambda (p) (and (near? p) (neighbor-posn? p)))
                                       mini-posn-swarm))
          (foldr (lambda (p accum) (v+ (get-repulsion-vector p) accum))
                 (make-posn 0 0)
                 edge-neighbors))))
    
    ;;-- Nominal speed behaviors ---
      
    ;; get-nominal-speed-vector:  -> posn
    ;; compute the steering vector that will tend to make me go in my
    ;; current direction at a nominal-speed
    (define (get-nominal-speed-vector)
      (v-scale (cond [(v-zero? vel) (* .2 nom-speed)]
		     [else (* .5 (- nom-speed (v-mag vel)))])
	       (v-norm vel)))
      
    ;;-- Combined vectors ---
      
    ;; get-new-velocity-vector: swarm -> posn
    ;; consumes a swarm and computes the appropriate
    ;; new vector after combining cohesion, alignment, separation, edges etc and clipping
    (define (get-new-velocity-vector s)
      (local ((define close (filter (lambda (c) (and (not (eq? (c 'loc) loc)) (near? (c 'loc)))) s))
              (define nh (get-my-neighbors close))
              (define others (get-others-close close))
              (define ot-vec (cond [(empty? others) (make-posn 0 0)]
                                   [else (v-scale AVOID-OTHER-TYPE-W
                                                  (v-norm (get-separation-vector others)))]))
	      (define edge-steer-vec (v-scale EDGE-W (v-norm (get-edge-vector))))
	      (define nom-vec (v-scale NOMINAL-SPEED-W (get-nominal-speed-vector))))
        (foldr v+
               vel
               (cond [(empty? nh)
                      (list edge-steer-vec nom-vec ot-vec)]
                     [else (list 
                            (v-scale ALIGNMENT-W (v-norm (get-alignment-vector nh)))
                            (v-scale COHESION-W (v-norm (get-cohesion-vector nh)))
                            (v-scale SEPARATION-W (v-norm (get-separation-vector nh)))
                            edge-steer-vec
                            nom-vec
                            ot-vec
                            )]))))
    
    ;; UPDATING AND MOVING
      
    ;; update-critter: swarm -> void
    ;; adjust the critter reflecting the movement based on the speed and heading
    (define (update-critter s)
      (begin
        (set! new-loc (v-mod! (v+ loc vel)))
        (set! new-vel (get-new-velocity-vector s))
        ))

    ;; move-critter:  -> critter
    ;; make the new location and velocity the current ones
    (define (move-critter)
      (begin
        (cond [killed-respawn 
               ;;(set! blood-spots (cons (bloodspot loc (* 3 CRITTER-RADIUS)) blood-spots))
               (set! loc (make-posn (add1 (random (sub1 WIDTH))) (add1 (random (sub1 HEIGHT)))))
               ;;(set! new-vel (make-posn (- (random 19) 9) (- (random 19) 9)))
               (set! killed-respawn #f)]
              [(positive? feeding) (set! feeding (sub1 feeding))]
              [else (set! loc new-loc)])
        (set! vel new-vel)
        service-manager))

    ;; SERVICE MANAGER
    ;; service-manager: symbol -> ...
    (define (service-manager msg)
      (cond [(symbol=? msg 'draw-on) (lambda (i) (display-critter i))]
	    [(symbol=? msg 'update-vel)
	     (lambda (s) (begin (update-critter s) true))]
	    [(symbol=? msg 'move) (move-critter)]
	    [(symbol=? msg 'loc) loc]
	    [(symbol=? msg 'vel) vel]
            [(symbol=? msg 'set-vel!) (lambda (new-v) (set! vel new-v))]
	    [(symbol=? msg 'type) type]
            [(symbol=? msg 'report-kills) n-kills]
	    [(symbol=? msg 'reset-kills) (set! n-kills 0)]
            [(symbol=? msg 'killed-respawn) (set! killed-respawn #t)]
            [(symbol=? msg 'killed?) killed-respawn]
            [else (error 'critter-service-manager (string-append "Invalid message given: " (symbol->string msg)))]))
    )
    service-manager))

;;----- MAIN

;; draw-swarm: swarm -> void
;; display the given swarm
(define (draw-swarm s)
  (foldl (lambda (c i)
           ((c 'draw-on) i))
         (empty-scene WIDTH HEIGHT)
         s))

;; update-swarm: swarm -> swarm
;; update each critter in the swarm
;; if want killed sheep to respawn, then the 1st, 2nd and 4th expressions - else the 1st and 3rd
(define (update-swarm s) 
  (for-each (lambda (x) ((x 'update-vel) s)) s)
  ;(for-each (lambda (x) (x 'move)) s)
  ;#|
  (foldl (lambda (c s)
           (if (not (c 'killed?))
               (cons (c 'move) s)
               s))
         empty s)
  ;|#
  ;s
  )

;; animate-swarm: swarm N -> true
;; draw, wait, clear, and update N times the given swarm
(define (animate-swarm s n)
  (big-bang s 
            (to-draw draw-swarm)
            (on-tick update-swarm DELAY n)))

(define-struct simstate (swarm kills time) #:mutable)
;; a simstate is a structure: (make-simstate s k t)
;; where s is a swarm, k is (listof N), and t is a N

;; ssw-simulate: swarm N -> sim-struct
;; similar to animate-swarm, but does not do any drawing/graphics -- thus, no big-bang --
;; and specific to sheep/sentinel/wolf swarms
(define (ssw-simulate s n)
  (local ((define ss (make-simstate s empty 0))
          ;; count-sheep: swarm -> N
          (define (count-sheep s)
            (length (filter (lambda (c) (symbol=? 'sheep (c 'type))) s)))
          (define n-sheep (count-sheep s))
          ;; sim-helper: simstate N -> ...
          (define (sim-helper ss i)
            (cond [(= i n) ss]
                  [(< (count-sheep (simstate-swarm ss)) (/ n-sheep 2)) ss]
                  [else (let ((new-swarm (update-swarm (simstate-swarm ss))))
                          (sim-helper (make-simstate new-swarm
                                                     (cons (cons (- (count-sheep (simstate-swarm ss)) 
                                                                    (count-sheep new-swarm))
                                                                 i)
                                                           (simstate-kills ss))
                                                     (add1 i))
                                      (add1 i)))]))
          (define final-ss (sim-helper ss 0)))
    (set-simstate-kills! final-ss 
                         (filter (lambda (pr) (positive? (car pr))) (simstate-kills final-ss)))
    final-ss))
    
                          

;; MISC

;; gen-critter: param-vec symbol symbol number -> critter
;; generate a random critter
(define (gen-critter pvec type col nom-speed)
  (make-critter
   pvec
   (make-posn (add1 (random (sub1 WIDTH))) (add1 (random (sub1 HEIGHT))))
   (local ((define v-vec (make-posn (- (random 19) 9) (- (random 19) 9))))
	  (if (v-zero? v-vec)
	      (make-posn 1 0)
	      v-vec))
   type
   col
   nom-speed))

;; gen-swarm: number -> swarm
;; takes a posn which serves as a center-of-mass, an average heading,
;; and a count, and creates a swarm of the given count number of critters
;; randomly centered around the center of mass with roughly the average heading
(define (gen-swarm count pvec type col nom-speed)
  (build-list count (lambda (x) (gen-critter pvec type col nom-speed))))

;;----- RUN

(define testswarm
  (list (make-critter type-b (make-posn 10 200) (make-posn 5 5) 'cool 'blue 3)
        (make-critter type-b (make-posn 30 200) (make-posn 5 5) 'cool 'blue 3)
        (make-critter type-b (make-posn 15 180) (make-posn 5 5) 'cool 'blue 3)))

(define (three-types n)
  (animate-swarm (append (gen-swarm 7 type-a 'foo 'red 8)
                         (gen-swarm 7 type-b 'cool 'blue 3)
                         (gen-swarm 7 type-c 'rad 'purple 5))
                 n))

(define wolves (gen-swarm 2 t-wolf 'wolf 'black 3))
(define sheep (gen-swarm 20 t-sheep 'sheep 'blue 3))
(define scouts (gen-swarm 2 t-sheep-scout 'sheep 'green 3))


;;----- TESTS 

;; make-sheep/wolves-flock: N N N -> swarm
;; create swarm/flock with s1 sheep, s2 scouts, and w wolves
(define (make-sheep/wolves-flock s1 s2 w)
  (append (gen-swarm s1 t-sheep 'sheep 'blue 3)
          (gen-swarm s2 t-sheep-scout 'sheep 'green 3)
          (gen-swarm w t-wolf 'wolf 'black 3)))

;; run-exp: N N N N N -> (listof simstate)
;; run a repeated experiment collecting the result
(define (run-exp s1 s2 w n-rep time-steps)
  (build-list 
   n-rep (lambda (_) 
           (ssw-simulate (make-sheep/wolves-flock s1 s2 w)
                         time-steps))))


;;----- SIMSTATE PROCESSORS

;; kill-count: simstate -> number
;; count the kills
(define (kill-count ss)
  (foldl (lambda (c t)
           (+ (if (symbol=? (c 'type) 'wolf)
                  (c 'report-kills)
                  0)
              t))
         0 (simstate-swarm ss)))

;; time-to-halve: simstate -> number
(define (time-to-halve ss) (simstate-time ss))


;;(three-types 400)
;;(wolves-and-sheep 400)

;(animate-swarm (append wolves sheep) 2000)
;(animate-swarm (append wolves scouts (drop sheep 2)) 2000)

(define r1 'fake)
(define r2 'fake)
;(set! r1 (run-exp 20 0 4 500 2000))
;(set! r2 (run-exp 19 1 4 500 2000))
#|
(define r20-0-4-200-3000 (run-exp 20 0 4 200 3000))

(define r19-1-4-200-3000 (run-exp 19 1 4 200 3000))
(define r30-0-4-200-3000 (run-exp 30 0 4 200 3000))
(define r29-1-4-200-3000 (run-exp 29 1 4 200 3000))
(define r40-0-4-200-3000 (run-exp 40 0 4 200 3000))
(define r39-1-4-200-3000 (run-exp 39 1 4 200 3000))
|#
;(define r100-0-4-200-4000 (run-exp 60 0 4 300 3000))
;(define r99-1-4-200-4000 (run-exp 59 1 4 300 3000))

;; output-to-R: (listof simstate) (simstate -> number) -> string
;; convert a results group using the given f into a string for processing with R
(define (output-to-R res f)
  (local ((define nums (map f res))
          )
    (string-append
     "= c(" (numbers->string nums) ")")))

;; output-to-CSV: (or? 'spawn 'nospawn) sheep sentinels wolves repeats time-duration (listof simtate) -> string
;; record the data for output to file and

;; numbers->string: (listof number) -> string
;; mash the numbers into CSV string
(define (numbers->string lon)
  (foldr (lambda (n out) (string-append (number->string n) "," out))
         (number->string (last lon))
         (drop-right lon 1)))


(animate-swarm (make-sheep/wolves-flock 30 2 4) 3000)