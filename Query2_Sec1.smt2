; ==============================================================================
; Example 3:
;
;    - Artifact name: Query2_Sec1.smt2
;    - Query: Get the number of enrolments.
;    - SQL implementation of the query: SELECT COUNT(*) FROM Enrolment;.
;    - Security policy:
;        + There is only one Role: Lecturer.
;        + Every lecturer can read any enrolment status 
;          if he/she is the oldest lecturer.
;            Lecturer.allInstances()->forAll(l|caller.age >= l.age).
;    Optimization scenario: If the user is the oldest lecturer, 
;    then no authorisation check is required when reading any enrolment status.
;
; ==============================================================================

(set-logic UFSLIA) ; set-logic only required for CVC4, 
                   ; Z3 detects automatically

; Mapping from datamodel to MSFOL theory
(declare-sort Classifier 0)
(declare-const nullClassifier Classifier)
(declare-const invalidClassifier Classifier)
(declare-const nullInt Int)
(declare-const invalidInt Int)
(declare-const nullString String)
(declare-const invalidString String)
(assert (distinct nullClassifier invalidClassifier))
(assert (distinct nullInt invalidInt))
(assert (distinct nullString invalidString))
(declare-fun Lecturer (Classifier) Bool)
(assert (not (Lecturer nullClassifier)))
(declare-fun Student (Classifier) Bool)
(assert (not (Student nullClassifier)))
(assert (not (Lecturer invalidClassifier)))
(declare-fun name_Lecturer (Classifier) String)
(assert (= (name_Lecturer nullClassifier) invalidString))
(assert (= (name_Lecturer invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (name_Lecturer x) invalidString))))
(declare-fun age_Lecturer (Classifier) Int)
(assert (= (age_Lecturer nullClassifier) invalidInt))
(assert (= (age_Lecturer invalidClassifier) invalidInt))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (age_Lecturer x) invalidInt))))
(declare-fun email_Lecturer (Classifier) String)
(assert (= (email_Lecturer nullClassifier) invalidString))
(assert (= (email_Lecturer invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Lecturer x)
        (distinct (email_Lecturer x) invalidString))))
(assert (not (Student invalidClassifier)))
(declare-fun email_Student (Classifier) String)
(assert (= (email_Student nullClassifier) invalidString))
(assert (= (email_Student invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (email_Student x) invalidString))))
(declare-fun name_Student (Classifier) String)
(assert (= (name_Student nullClassifier) invalidString))
(assert (= (name_Student invalidClassifier) invalidString))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (name_Student x) invalidString))))
(declare-fun age_Student (Classifier) Int)
(assert (= (age_Student nullClassifier) invalidInt))
(assert (= (age_Student invalidClassifier) invalidInt))
(assert (forall ((x Classifier))
    (=> (Student x)
        (distinct (age_Student x) invalidInt))))
(declare-fun Enrolment (Classifier Classifier) Bool)
(assert (forall ((x Classifier))
    (forall ((y Classifier)) 
        (=> (Enrolment x y) 
            (and (Lecturer x) (Student y))))))
(assert (forall ((x Classifier)) 
    (=> (Lecturer x) (not (Student x)))))
(assert (forall ((x Classifier)) 
    (=> (Student x) (not (Lecturer x)))))
; End mapping from datamodel to MSFOL

; Declaring user, and objects to be read
(declare-const kcaller Classifier)
(assert (Lecturer kcaller)) ; caller has the role Lecturer
(declare-const klecturers Classifier)
(assert (Lecturer klecturers)) ; object ends to be read 
(declare-const kstudents Classifier)
(assert (Student kstudents)) ; object ends to be read 
; End declaring user, and objects to be read

; if the caller is the oldest lecturer
; Lecturer.allInstances()->forAll(l|l.age <= caller.age)
(assert (forall ((l Classifier))
    (and (=> (Lecturer l) 
             (and (<= (age_Lecturer l) (age_Lecturer kcaller)) 
                  (not (or (= (age_Lecturer l) nullInt) 
                           (or (= l nullClassifier) (= l invalidClassifier)) 
                           (= (age_Lecturer kcaller) nullInt) 
                           (or (= kcaller nullClassifier) 
                               (= kcaller invalidClassifier)))))) 
         (not false))))
         
; not (map_def(auth(Lecturer, age)) => map_true(auth(Lecturer, age))) 
; auth(Lecturer,age) = 
;   Lecturer.allInstances()->select(l|l.age > kcaller.age)->isEmpty()
(declare-fun TEMP0 (Classifier) Bool)
(assert (forall ((l Classifier)) 
    (= (TEMP0 l) 
       (and (Lecturer l) 
            (and (> (age_Lecturer l) (age_Lecturer kcaller)) 
                 (not (or (= (age_Lecturer l) nullInt) 
                          (or (= l nullClassifier) (= l invalidClassifier)) 
                          (= (age_Lecturer kcaller) nullInt) 
                          (or (= kcaller nullClassifier) 
                          (= kcaller invalidClassifier)))))))))

(assert (not (forall ((x Classifier)) 
    (and (not (TEMP0 x)) (not false)))))

; Checking for satisfiability
(check-sat)
