# Artifacts Submission for Manuscript [SoSym22]

**Manuscript**: "Optimising Fine-Grained Access Control Policy Enforcement for Database Queries: A Model-Driven Approach"

## Table of Contents

- [Requirements](#requirements)
- [Experiments](#experiments)
    - [Experiment 1](#example-1)
    - [Experiment 2](#example-2)
    - [Experiment 3](#example-3)
    - [Experiment 4](#example-4)
- [How to run the artifacts](#how-to-run-the-artifacts)
    - [CVC4](#cvc4)
    - [Z3](#z3)

## Requirements
The following artifacts are MSFOL theories written in SMT-LIB2 language.
Therefore, the following SMT solvers are recommended to be installed in advance in order to replicate the experiments:
- [CVC4](https://github.com/CVC4/CVC4-archived)
- [Z3](https://github.com/Z3Prover/z3)

## Experiments
In this manuscript, we provide a number of examples to showcase our methodology of proving that, given a query,
in some scenarios the OCL authorisation constraints can be proven to be unnecessary, and therefore can be safely 
"skipped" during the secured execution of q. The following items describe in short the examples:

### Example 1:
- Artifact name: Query1_Sec1.smt2
- Query: Get the number of students whose age is greater than 18.
- SQL implementation of the query: `SELECT COUNT(*) FROM Student WHERE age > 18;`.
- Security policy: 
  - There is only one Role: `Lecturer`.
  - Every lecturer can read the age of the student if he/she is the oldest lecturer.
    - OCL authorisation constaint: `Lecturer.allInstances()->forAll(l|caller.age >= l.age)`.
- Optimization scenario: If the user is the oldest lecturer, then no authorisation check is required when reading the age of students.

### Example 2:
- Artifact name: Query1_Sec2.smt2
- Query: Get the number of students whose age is greater than 18.
- SQL implementation of the query: `SELECT COUNT(*) FROM Student WHERE age > 18;`.
- Security policy: 
  - There is only one Role: `Lecturer`.
  - Every lecturer can read his/her own students' age.
    - OCL authorisation constaint: `caller.students->exists(s|s = self)`.
- Optimization scenario: If the user teaches every student, then no authorisation check is required when reading the age of students.

### Example 3:
- Artifact name: Query2_Sec1.smt2
- Query: Get the number of  enrolments.
- SQL implementation of the query: `SELECT COUNT(*) FROM Enrolment;`.
- Security policy: 
  - There is only one Role: `Lecturer`.
  - Every lecturer can read any enrolment status if he/she is the oldest lecturer.
    - OCL authorisation constaint: `Lecturer.allInstances()->forAll(l|caller.age >= l.age)`.
- Optimization scenario: If the user is the oldest lecturer, then no authorisation check is required when reading any enrolment status.

### Example 4:
- Artifact name: Query2_Sec2.smt2
- Query: Get the number of  enrolments.
- SQL implementation of the query: `SELECT COUNT(*) FROM Enrolment;`.
- Security policy: 
  - There is only one Role: `Lecturer`.
  - Every lecturer can read his/her own students' age.
    - OCL authorisation constaint: `caller.students->exists(s|s = students)`.
- Optimization scenario: If the user teaches every student, then no authorisation check is required when reading any enrolment status.

## How to run the artifacts

### CVC4
For CVC4 users, the following command would prove the theory:
```
cvc4.exe -finite-model-find <THEORY_NAME>
```

### Z3
For Z3 users, the following command would prove the theory:
```
z3 <THEORY_NAME>
```
**Note**: There may be some warnings being output by the solvers but they do no harm so please ignore them.
