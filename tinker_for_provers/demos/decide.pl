% =========================================================================
% MINIMAL INTERFACE decide/1
% =========================================================================

decide(Left <=> Right) :- !,
    % VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide_silent(Left => Right, _, Logic1),
        decide_silent(Right => Left, _, Logic2)
    )),
    write('Direction 1 ('), write(Left => Right), write(') is valid in '), 
    write(Logic1), write(' logic'), nl,
    write('Direction 2 ('), write(Right => Left), write(') is valid in '), 
    write(Logic2), write(' logic'), nl,
    !.

decide(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    ( is_classical_pattern(F2) ->
        time(provable_at_level([] > [F2], classical, _)),
        write('Valid in classical logic'), nl
    ;
        time(progressive_proof_silent(F2, _, Logic)),
        write('Valid in '), write(Logic), write(' logic'), nl
    ),
    !.

% decide/1 for sequents
decide(G > D) :-
    G \= [], !,
    % VALIDATION
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        time(provable_at_level(PrepG > PrepD, classical, _)),
        write('Valid in classical logic'), nl
    ; time(provable_at_level(PrepG > PrepD, minimal, _)) ->
        write('Valid in minimal logic'), nl
    ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
        ( proof_uses_lbot(Proof) -> 
            write('Valid in intuitionistic logic'), nl
        ; 
            write('Valid in intuitionistic logic'), nl
        )
    ;
        time(provable_at_level(PrepG > PrepD, classical, _)),
        write('Valid in classical logic'), nl
    ),
    !.

% Equivalence for decide
decide([Left] <> [Right]) :- !,
    % VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        prove_sequent_silent([Left] > [Right], _, Logic1),
        prove_sequent_silent([Right] > [Left], _, Logic2)
    )),
    write('Direction 1 ('), write(Left), write(' |- '), write(Right), write(') is valid in '), 
    write(Logic1), write(' logic'), nl,
    write('Direction 2 ('), write(Right), write(' |- '), write(Left), write(') is valid in '), 
    write(Logic2), write(' logic'), nl,
    !.
