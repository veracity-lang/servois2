# Predicate selection example

### Decide which predicate to use: 

    P1: (= contents 0)
    P2: (> contents 0)

### Four queries:

 * `p1-commute.smtlib2` -     check whether P1 implies incr/decr commute
 * `p1-not-commute.smtlib2` - check whether P1 implies incr/decr don't commute
 * `p2-commute.smtlib2` -     check whether P2 implies incr/decr commute
 * `p2-not-commute.smtlib2` - check whether P2 implies incr/decr don't commute

### Running these with CVC4:

```
cvc4 --lang smtlib2 p1-commute.smtlib2 --produce-models # Should be "sat"
cvc4 --lang smtlib2 p1-not-commute.smtlib2 --produce-models # Should be "unsat"
cvc4 --lang smtlib2 p2-commute.smtlib2 --produce-models # Should be "unsat"
cvc4 --lang smtlib2 p2-not-commute.smtlib2 --produce-models # Should be "sat"
```