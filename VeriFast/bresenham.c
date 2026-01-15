// verifast_options{disable_overflow_check}

#include "stdlib.h"

/**
    Daten:

    data Bres = {
        dx :: Int,
        dy :: Int,
        incE :: Int,
        IncNE :: Int,
    }

    data Signal = Pulse | NoPulse

    data Step = {
        x :: Int,
        y :: Int,
        d :: Int,
        signal :: Signal,
    }

    Funktionen:

    init :: Int -> Int -> (Bres, Step)
    step :: Bres -> Step -> Step
    bresenham :: Int -> Int -> [Step]


    VeriFast Vokabular:

    - pre conditions:   requires E;
    - post conditions:  ensures E;
    - assertions:       assert E;
    - invariants:       invariant E;
    - predicates:       predicate(args) = E;
    - lemmas:           lemma void lem(args) requires E1; ensures E2; { <proof> }
    - fixpoints:        fixpoint type fn(args) { <body> }

    Prädikate:

    - open pred(args)   Öffnen gewährt VeriFast Zugriff auf die enthaltenen Annahmen/Aussagen
    - close pred(args)  Schließen leitet das Prädikat aus den lokalen Annahmen etc. her;
                        Schließen konsumiert die verwendeten Fakten

    Zugriff auf Memory:

    - Struct_mem_(ptr, _) bezeichnet Ownership für (und damit Zugriff auf) das Feld <mem> in der struct an Adresse <ptr> vom Typ <Struct>
    - Struct_mem(ptr, ?x) bindet das Feld <mem> in <ptr> (vom Typ <Struct>) an die Ghost Variable <x>
    - Struct_mem(ptr, v)  besagt, dass das Feld <mem> in <ptr> (vom Typ <Struct>) den Wert <v> hat

    - eine Funktion muss Ownership für alle Heap Chunks, auf die sie (lesend/schreibend) zugreift, besitzen
    - Ownership von Heap Chunks muss per ensures wieder abgegeben werden

*/

typedef enum { Pulse, NoPulse } Signal;

typedef struct {
    int dx;
    int dy;
    int x;
    int y;
    int d;
    int incE;
    int incNE;
    Signal signal;
} Bres;

/*@

predicate bres_access(Bres *b) =
    Bres_dx_(b, _)      &*&
    Bres_dy_(b, _)      &*&
    Bres_x_(b, _)       &*&
    Bres_y_(b, _)       &*&
    Bres_d_(b, _)       &*&
    Bres_incE_(b, _)    &*&
    Bres_incNE_(b, _)   &*&
    Bres_signal_(b, _)
;

fixpoint int err(int dx, int dy, int x, int y) {
    return 2*dy*x - 2*dx*y;
}

predicate bres_state(Bres *b, int dx, int dy, int x, int y, int d, Signal s) =
    b->dx     |-> dx            &*&
    b->dy     |-> dy            &*&
    b->x      |-> x             &*&
    b->y      |-> y             &*&
    b->d      |-> d             &*&
    b->incE   |-> 2*dy          &*&
    b->incNE  |-> 2*(dy - dx)   &*&
    b->signal |-> s             &*&

    // basic bounds/shape
    0 <= dy &*& dy <= dx &*&    // Note: both dy == 0 and dy == dx edge cases are indeed fine
    0 <= x &*&                  // follows from initial state and x_i == x_(i-1) + 1
    0 <= y &*&                  // follows from initial state and y_i == y_(i-1) || y_i == y_(i-1) + 1

    // "Bresenham" invariant of d
    d == 2*dy*x - 2*dx*y + 2*dy - dx &*&

    // Pixel correctness invariant: 2*dx*y - dx <= 2*dy*x <= 2*dx*y + dx
    -dx <= err(dx, dy, x, y) &*& err(dx, dy, x, y) <= dx
;

@*/

void init(int x, int y, Bres *b)
    //@ requires bres_access(b) &*& 0 <= y &*& y <= x;
    //@ ensures bres_state(b, x, y, 0, 0, 2*y - x, NoPulse);
{
    //@ open bres_access(b);
    b->dx = x;
    b->dy = y;
    b->x = 0;
    b->y = 0;
    b->d = 2*y - x;
    b->incE = 2*y;
    b->incNE = 2*(y - x);
    b->signal = NoPulse;
    //@ close bres_state(b, x, y, 0, 0, 2*y - x, NoPulse);
}

void step(Bres *b)
    //@ requires bres_state(b, ?dx, ?dy, ?x, ?y, _, _);
    //@ ensures bres_state(b, dx, dy, x+1, _, _, _);
{
    //@ open bres_state(b, _, _, _, _, _, _);
    if (b->d < 0) {
        b->x += 1;
        b->d += b->incE;
        b->signal = Pulse;
        //@ close bres_state(b, _, _, x+1, y, _, Pulse);
    } else {
        b->x += 1;
        b->y += 1;
        b->d += b->incNE;
        b->signal = NoPulse;
        //@ close bres_state(b, _, _, x+1, y+1, _, NoPulse);
    }
}

void bresenham(int lowerRateLimitBpm, int intrinsicRateBpm)
    //@ requires 0 <= intrinsicRateBpm &*& intrinsicRateBpm <= lowerRateLimitBpm;
    //@ ensures true;
{
    Bres state;
    //@ close bres_access(&state);
    init(lowerRateLimitBpm, intrinsicRateBpm, &state);
    while (1)
        //@ invariant bres_state(&state, lowerRateLimitBpm, intrinsicRateBpm, _, _, _, _);
    {
        step(&state);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    bresenham(80, 60);
    return 0;
}
