% =========================================================================
% QUINE_G4MIC.PL - Propositional Logic Filter with Countermodels
% =========================================================================
% Based on Jan Burse's Quine algorithm implementation
% Adapted for G4-mic syntax
%
% Copyright (C) 2025 Joseph Vidal-Rosset
% Licensed under GNU GPL v3+
% =========================================================================

:- module(quine_g4mic, [
    pre_check_propositional/2,
    quine_decide/2,
    is_propositional/1,
    check_formula/1,
    test_quine/0
]).

:- use_module(library(lists)).

% =========================================================================
% OPERATORS - Same as G4-mic
% =========================================================================
:- op( 500, fy, ~).
:- op(1000, xfy, &).
:- op(1100, xfy, '|').
:- op(1110, xfy, =>).
:- op(1120, xfy, <=>).

% =========================================================================
% PROPOSITIONAL DETECTION  
% =========================================================================

is_propositional(F) :-
    \+ contains_quantifier(F).

contains_quantifier(![_-_]:_) :- !.
contains_quantifier(?[_-_]:_) :- !.
contains_quantifier(~A) :- !, contains_quantifier(A).
contains_quantifier(A & B) :- !, (contains_quantifier(A) ; contains_quantifier(B)).
contains_quantifier(A | B) :- !, (contains_quantifier(A) ; contains_quantifier(B)).
contains_quantifier(A => B) :- !, (contains_quantifier(A) ; contains_quantifier(B)).
contains_quantifier(A <=> B) :- !, (contains_quantifier(A) ; contains_quantifier(B)).
contains_quantifier(_) :- fail.

% =========================================================================
% MAIN INTERFACE
% =========================================================================

pre_check_propositional(Formula, Result) :-
    ( is_propositional(Formula) ->
        quine_decide(Formula, Result)
    ;
        Result = not_propositional
    ).

quine_decide(Formula, Result) :-
    collect_prop_atoms(Formula, Atoms),
    ( Atoms = [] ->
        eval_ground(Formula, Value),
        ( Value == 1 -> Result = tautology
        ; Value == 0 -> Result = antilogy
        ; Result = error
        )
    ;
        quine_taut(Formula, Atoms, TruthValue, Countermodel),
        interpret_result(TruthValue, Countermodel, Result)
    ).

interpret_result(1, _, tautology) :- !.
interpret_result(0, _, antilogy) :- !.
interpret_result(_, Model, contingent(Model)) :- !.

% =========================================================================
% PROPOSITIONAL ATOM COLLECTION
% =========================================================================

collect_prop_atoms(Formula, SortedAtoms) :-
    collect_atoms(Formula, Atoms),
    sort(Atoms, SortedAtoms).

collect_atoms(A, [A]) :- 
    atom(A), 
    \+ member(A, [~, &, '|', =>, <=>, #, 1, 0]),
    !.
collect_atoms(#, []) :- !.
collect_atoms(~A, Atoms) :- !, collect_atoms(A, Atoms).
collect_atoms(A & B, Atoms) :- !,
    collect_atoms(A, AtomsA),
    collect_atoms(B, AtomsB),
    append(AtomsA, AtomsB, Atoms).
collect_atoms(A | B, Atoms) :- !,
    collect_atoms(A, AtomsA),
    collect_atoms(B, AtomsB),
    append(AtomsA, AtomsB, Atoms).
collect_atoms(A => B, Atoms) :- !,
    collect_atoms(A, AtomsA),
    collect_atoms(B, AtomsB),
    append(AtomsA, AtomsB, Atoms).
collect_atoms(A <=> B, Atoms) :- !,
    collect_atoms(A, AtomsA),
    collect_atoms(B, AtomsB),
    append(AtomsA, AtomsB, Atoms).
collect_atoms(_, []).

% =========================================================================
% QUINE ALGORITHM
% =========================================================================

quine_taut(Formula, [], Formula, []) :- !.
quine_taut(Formula, [Atom|RestAtoms], Result, Countermodel) :-
    copy_term(Formula-[Atom|RestAtoms], F1-[1|RestAtoms]),
    eval(F1, E1),
    
    copy_term(Formula-[Atom|RestAtoms], F0-[0|RestAtoms]),
    eval(F0, E0),
    
    simp(E1 & E0, Combined),
    
    quine_taut(Combined, RestAtoms, Result, PartialModel),
    
    ( Result == 1 ->
        Countermodel = PartialModel
    ; Result == 0 ->
        Countermodel = PartialModel
    ;
        ( eval_with_subst(Formula, [Atom-0|PartialModel], 0) ->
            Countermodel = [Atom-0|PartialModel]
        ;
            Countermodel = [Atom-1|PartialModel]
        )
    ).

% =========================================================================
% EVALUATION
% =========================================================================

eval(A, A) :- integer(A), !.
eval(A, A) :- atom(A), \+ member(A, [#, ~, &, '|', =>, <=>]), !.
eval(#, 0) :- !.
eval(~A, R) :- !, eval(A, X), simp(~X, R).
eval(A & B, R) :- !, eval(A, X), eval(B, Y), simp(X & Y, R).
eval(A | B, R) :- !, eval(A, X), eval(B, Y), simp(X | Y, R).
eval(A => B, R) :- !, eval(A, X), eval(B, Y), simp(X => Y, R).
eval(A <=> B, R) :- !, eval(A, X), eval(B, Y), simp(X <=> Y, R).
eval(A, A).

eval_ground(#, 0) :- !.
eval_ground(~A, R) :- !, eval_ground(A, X), (X = 1 -> R = 0 ; R = 1).
eval_ground(A & B, R) :- !, eval_ground(A, X), eval_ground(B, Y), 
    (X = 1, Y = 1 -> R = 1 ; R = 0).
eval_ground(A | B, R) :- !, eval_ground(A, X), eval_ground(B, Y),
    (X = 1 -> R = 1 ; Y = 1 -> R = 1 ; R = 0).
eval_ground(A => B, R) :- !, eval_ground(A, X), eval_ground(B, Y),
    (X = 0 -> R = 1 ; Y = 1 -> R = 1 ; R = 0).
eval_ground(A <=> B, R) :- !, eval_ground(A, X), eval_ground(B, Y),
    (X = Y -> R = 1 ; R = 0).
eval_ground(A, _) :- 
    atom(A),
    format('ERROR: Unbound atom ~w~n', [A]),
    fail.

eval_with_subst(Formula, Subst, Result) :-
    apply_subst(Formula, Subst, SubstFormula),
    eval_ground(SubstFormula, Result).

apply_subst(A, Subst, V) :- 
    atom(A), 
    member(A-V, Subst), !.
apply_subst(A, _, A) :- 
    atom(A), !.
apply_subst(#, _, 0) :- !.
apply_subst(~A, Subst, ~SA) :- !, apply_subst(A, Subst, SA).
apply_subst(A & B, Subst, SA & SB) :- !,
    apply_subst(A, Subst, SA),
    apply_subst(B, Subst, SB).
apply_subst(A | B, Subst, SA | SB) :- !,
    apply_subst(A, Subst, SA),
    apply_subst(B, Subst, SB).
apply_subst(A => B, Subst, SA => SB) :- !,
    apply_subst(A, Subst, SA),
    apply_subst(B, Subst, SB).
apply_subst(A <=> B, Subst, SA <=> SB) :- !,
    apply_subst(A, Subst, SA),
    apply_subst(B, Subst, SB).

% =========================================================================
% SIMPLIFICATION
% =========================================================================

simp(A, A) :- integer(A), !.
simp(A, A) :- atom(A), !.
simp(~0, 1) :- !.
simp(~1, 0) :- !.
simp(~A, ~A) :- !.
simp(0 & _, 0) :- !.
simp(_ & 0, 0) :- !.
simp(1 & B, B) :- !.
simp(A & 1, A) :- !.
simp(A & B, A & B) :- !.
simp(1 | _, 1) :- !.
simp(_ | 1, 1) :- !.
simp(0 | B, B) :- !.
simp(A | 0, A) :- !.
simp(A | B, A | B) :- !.
simp(0 => _, 1) :- !.
simp(_ => 1, 1) :- !.
simp(1 => B, B) :- !.
simp(A => 0, R) :- !, simp(~A, R).
simp(A => B, A => B) :- !.
simp(0 <=> B, R) :- !, simp(~B, R).
simp(B <=> 0, R) :- !, simp(~B, R).
simp(1 <=> B, B) :- !.
simp(A <=> 1, A) :- !.
simp(A <=> B, A <=> B) :- !.

% =========================================================================
% DISPLAY
% =========================================================================

display_countermodel([]) :- 
    write('  (empty valuation)'), nl.
display_countermodel(Model) :-
    write('  Countermodel: '), nl,
    display_valuation(Model).

display_valuation([]).
display_valuation([Atom-Value|Rest]) :-
    format('    ~w = ~w~n', [Atom, Value]),
    display_valuation(Rest).

find_minimal_countermodel(Formula, MinimalModel) :-
    collect_prop_atoms(Formula, Atoms),
    findall(Model-Count, 
            (generate_model(Atoms, Model),
             eval_with_subst(Formula, Model, 0),
             count_true(Model, Count)),
            ModelsWithCount),
    ( ModelsWithCount = [] ->
        fail
    ;
        sort(2, @=<, ModelsWithCount, [MinimalModel-_|_])
    ).

generate_model([], []).
generate_model([A|As], [A-0|Model]) :- generate_model(As, Model).
generate_model([A|As], [A-1|Model]) :- generate_model(As, Model).

count_true([], 0).
count_true([_-0|Rest], Count) :- !, count_true(Rest, Count).
count_true([_-1|Rest], Count) :- 
    count_true(Rest, RestCount),
    Count is RestCount + 1.

% =========================================================================
% USER INTERFACE
% =========================================================================

check_formula(Formula) :-
    write('Checking: '), write(Formula), nl,
    ( is_propositional(Formula) ->
        quine_decide(Formula, Result),
        report_result(Formula, Result)
    ;
        write('Formula contains quantifiers - not propositional.'), nl
    ).

report_result(_Formula, tautology) :-
    write('Result: TAUTOLOGY'), nl,
    write('  → Passing to G4-mic for formal proof.'), nl.

report_result(_, antilogy) :-
    write('Result: ANTILOGY (always false)'), nl.

report_result(Formula, contingent(Model)) :-
    write('Result: CONTINGENT (not a theorem)'), nl,
    write('  → Countermodel found:'), nl,
    display_countermodel(Model),
    nl,
    ( find_minimal_countermodel(Formula, MinModel) ->
        write('  → Minimal countermodel:'), nl,
        display_countermodel(MinModel)
    ;
        true
    ).

% =========================================================================
% TESTS
% =========================================================================

test_quine :-
    write('=== QUINE G4-MIC TESTS ==='), nl, nl,
    
    write('Test 1: Tautology (p | ~p)'), nl,
    check_formula(p | ~p), nl,
    
    write('Test 2: Antilogy (p & ~p)'), nl,
    check_formula(p & ~p), nl,
    
    write('Test 3: Contingent (p => q)'), nl,
    check_formula(p => q), nl,
    
    write('Test 4: Peirce ((p => q) => p) => p'), nl,
    check_formula(((p => q) => p) => p), nl.

