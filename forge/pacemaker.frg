#lang forge/froglet
-- Idealized pacemaker algorithm for bradycardia
-- based on Bresenham algorithm

abstract sig Signal {}
one sig Pulse, NoPulse extends Signal {}

sig TraceStep {
    x: one Int, -- natural beat
    y: one Int, -- from Bresenham algorithm, not really necessary
    signal: one Signal,
    d: one Int
}

one sig Trace {
    dy: one Int, -- target heartbeat frequency
    dx: one Int, -- natural heartbeat frequency

    initialStep: one TraceStep,
    nextStep: pfunc TraceStep -> TraceStep,

    -- cached algorithm parameters
    dInc1: one Int,
    dInc2: one Int
}

pred okTrace {
    Trace.dx > 0
    Trace.dy > 0
    -- make problem a bit simpler
    Trace.dx > Trace.dy
}

-- initialize algorithm parameters
pred initTrace {
    Trace.dInc1 = multiply[Trace.dy, 2]
    Trace.dInc2 = multiply[subtract[Trace.dy, Trace.dx], 2]
 }

-- initialize first step
pred initStep[step: TraceStep] {
    step.x = 0
    step.y = 0
    step.d = subtract[multiply[Trace.dy, 2], Trace.dx]
}

-- single step, no pulse
pred no_pulse[pre, post: TraceStep] {
    pre.d < 0
    post.d = add[pre.d, Trace.dInc1]
    post.y = pre.y
    post.signal = NoPulse
}

pred pulse[pre, post: TraceStep] {
    pre.d >= 0
    post.d = add[pre.d, Trace.dInc2]
    post.y = add[pre.y, 1]
    post.signal = Pulse
}

pred next[pre, post: TraceStep] {
    post.x < Trace.dx
    post.x = add[pre.x, 1]
    Trace.nextStep[pre] = post
    no_pulse[pre, post] or pulse[pre, post]
}

pred bresenham { 
    okTrace
    initTrace
    initStep[Trace.initialStep]
    -- only one initial step
    no otherStep: TraceStep | Trace.nextStep[otherStep] = Trace.initialStep
    -- all steps are part of the algorithm
    all step: TraceStep | {
        step = Trace.initialStep or
        { one pre: TraceStep | next[pre, step] }
    }
    -- nextStep is nothing but next
    all pre: TraceStep | some Trace.nextStep[pre] => next[pre, Trace.nextStep[pre]]
    -- actually run to the end
    some step: TraceStep | step.x = subtract[Trace.dx, 1]
}

pred finalStep[step: TraceStep] {
    no Trace.nextStep[step]
}

any_pacemaker: run {
    bresenham
}  for 5 Int, exactly 4 TraceStep -- for {nextStep is plinear}

one_pacemaker: run {
    bresenham
    Trace.dx = 5
    Trace.dy = 2
}  for 8 Int, 8 TraceStep -- for {nextStep is plinear}

check_frequency: check {
    bresenham =>
    { all step: TraceStep | finalStep[step] => abs[subtract[Trace.dy, step.y]] <= 1 }
} for 8 Int, 5 TraceStep

check_distribution: check {
    bresenham =>
    { all step: TraceStep | abs[subtract[multiply[step.x, Trace.dy], multiply[step.y, Trace.dx]]] 
                              < Trace.dx }
} for 8 Int, 4 TraceStep
