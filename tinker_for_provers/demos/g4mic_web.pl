% =========================================================================
% COMMON OPERATORS - Centralized module
% To include in all prover modules
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
% =========================================================================
% TPTP OPERATORS (input syntax)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quanti
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% Input syntax: sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% =========================================================================
% LATEX OPERATORS (formatted output)
% ATTENTION: Respect spaces exactly!
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % space for quantifiers
:- op(400, fx, ' \\bot ').      % falsity (#)
% LaTeX syntax: sequent turnstile  
:- op(1150, xfx, ' \\vdash ').
% =========================================================================
% STARTUP BANNER
% =========================================================================
% Disable automatic SWI-Prolog banner
:- set_prolog_flag(verbose, silent).

%
:- initialization(show_banner).

show_banner :-
    write('Welcome to SWI-Prolog (32 bits, version 9.3.34-20-g3517bc35f)'),nl,
    write('SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.'),nl,
    write('For legal details and online help, see https://www.swi-prolog.org'),nl,nl,

    write('*****************************************************************'), nl,
    write('*                   G4-mic F.O.L. PROVER  -  1.0                *'), nl,
    write('*         (mic: minimal, intuitionistic and classical logic)    *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('Because g4mic_web.pl is a Prolog program:'),nl,
    write('never forget the dot at the end of each request!'),nl,nl,
    write('Usage:'),nl,
    write('  prove(Formula).  - proof in three styles, with shareable URLs'), nl,
    write('  decide(Formula). - concise mode '), nl,
    write('  help.            - show help'), nl,
    write('  examples.        - show examples'),nl.
% =========================================================================
% ITERATION LIMITS CONFIGURATION
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 15).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 5).
logic_iteration_limit(fol, 15).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% THEOREM vs SEQUENT DETECTION (simplified)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================

% normalize_formula/2: Apply efficiency-improving transformations
normalize_formula(Formula, Normalized) :-
    normalize_double_negations(Formula, F1),
    normalize_biconditional_order(F1, Normalized).

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :- 
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 2.
formula_complexity(A => B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.
contains_classical_pattern(![_-_]:A) :-
    contains_classical_pattern(A), !.
contains_classical_pattern(?[_-_]:A) :-
    contains_classical_pattern(A), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :- 
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================

% NEW: Automatic detection for sequents with premisses
prove(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
     %  VALIDATION: Verify premisses and conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent '), nl,
    nl,
    
    % Store premisses for display
    retractall(premiss_list(_)),
    assertz(premiss_list(G)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),
    
    % Prepare formulas
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    % Detect classical pattern in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   Constructive proof found in MINIMAL LOGIC '), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('    Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            write('    Proof found in CLASSICAL LOGIC '), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).

% Biconditionals - REGROUPES PAR TYPE
prove(Left <=> Right) :- !,
         % VALIDATION: Verify both directions
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Left => Right)),
    time((decide_silent(Left => Right, Proof1, Logic1))),
    
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Right => Left)),
    time((decide_silent(Right => Left, Proof2, Logic2))),
    
    nl,
    write('=== BICONDITIONAL: Proving both directions ==='), nl,nl,
    % output_logic_label(Logic1), nl, nl,
  %  write('    '), portray_clause(Proof1), nl,nl,
   %  output_logic_label(Logic2), nl, nl,
  % write('    '), portray_clause(Proof2), nl,nl,
  % write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof1), nl, nl,
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof1),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof2),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    write('This biconditional is valid:'), nl,
    write('- Direction 1 ('), write(Left => Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right => Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.


% Sequent equivalence: [A] <> [B] proves [A] > [B] AND [B] > [A]
prove([Left] <> [Right]) :- !,
          % VALIDATION: Verify both formulas
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    % Direction 1: Left > Right
    assertz(current_proof_sequent([Left] > [Right])),
    time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))),   
    % Direction 2: Right > Left
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))),
    nl,
    write('=== SEQUENT EQUIVALENCE: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
  %  write('    '), portray_clause(Proof1), nl, nl,
    output_logic_label(Logic2), nl, nl,
  %  write('    '), portray_clause(Proof2), nl, nl,
  %  write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,

    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Left])),
    render_nd_tree_proof(Proof1), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Right])),
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,

    % FITCH STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Left])),
    g4_to_fitch_sequent(Proof1, [Left] > [Right]),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Right])),
    g4_to_fitch_sequent(Proof2, [Right] > [Left]),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
       
    write('This sequent equivalence is valid:'), nl,
    write('- Direction 1 ('), write(Left), write(' |- '), write(Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right), write(' |- '), write(Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.

% Theorems (original logic)
prove(Formula) :-
         % VALIDATION: Verify the formula
    validate_and_warn(Formula, _ValidatedFormula),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR: '), write(Formula), nl,
    write('------------------------------------------'), nl,  
    write('MODE: Theorem '), nl,
    nl,
    
    retractall(premiss_list(_)),
    retractall(current_proof_sequent(_)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        write('=== DOUBLE NEGATION DETECTED ==='), nl,
        write('    -> Trying constructive first'), nl,
        write('=== TRYING CONSTRUCTIVE LOGIC ==='), nl,
        ( time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( time(provable_at_level([] > [F2], minimal, _)) ->
                write('  Constructive proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                )
            )
        ;
            write('    Constructive logic failed'), nl,
            write('=== FALLBACK: CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('   Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ; is_classical_pattern(F2) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Skipping constructive logic'), nl,
        write('=== TRYING CLASSICAL LOGIC ==='), nl,
        time(provable_at_level([] > [F2], classical, Proof)),
        write('   Classical proof found'), nl,
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level([] > [F2], minimal, Proof)) ->
            write('   Proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  -> Uses explosion explosion rule - Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            ;
                write('  -> No explosion -> INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            )
        ;
            write('   Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('  Proof found in Classical logic'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, Formula, theorem).

% =========================================================================
% HELPERS
% =========================================================================

% Prepare a list of formulas
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Compact display of a sequent
write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% FORMULA AND SEQUENT VALIDATION
% =========================================================================

% Validate a sequent (premisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Validate all premisses
    forall(member(Premiss, G), validate_and_warn(Premiss, _)),
    % Validate all conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    output_logic_label(LogicType),
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    ( Mode = sequent ->
        g4_to_fitch_sequent(Proof, OriginalFormula)
    ;
        g4_to_fitch_theorem(Proof)
    ),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    !.

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], minimal, Proof) ->
        Logic = minimal
    ; provable_at_level([] > [Formula], intuitionistic, Proof) ->
        Logic = intuitionistic
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL
% =========================================================================

provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    ( prove(Gamma > Delta, [], Threshold, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; prove(Gamma > Delta, [], Threshold, 1, _, intuitionistic, P)     % <- Then intuitionistic if failure
    ),
    !.

provable_at_level(Sequent, LogicLevel, Proof) :-
    logic_iteration_limit(LogicLevel, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    prove(Gamma > Delta, [], Threshold, 1, _, LogicLevel, Proof),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================

% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (Gamma > Delta),
    prepare_sequent_formulas(Gamma, Delta, PrepGamma, PrepDelta),
    ( member(SingleGoal, PrepDelta), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepGamma > PrepDelta, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepGamma > PrepDelta, intuitionistic, Proof) ->
        Logic = intuitionistic
    ;
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ).

output_logic_label(minimal) :- 
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :- 
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :- 
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).
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

% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('*****************************************************************'), nl,
    write('*                      G4 PROVER GUIDE                          *'), nl,
    write('*****************************************************************'), nl,
    write('## MAIN COMMANDS '), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  decide(Formula).           - says either true or false'), nl,
    write('## SYNTAX EXAMPLES '), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P '), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P , Q |- P & Q '), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('    prove(p <> ~ ~ p).                 - Bi-implication of Double Negation (sequents)'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS '), nl,
    write('  ~ A , (A & B) , (A | B) , (A => B) , (A <=> B) ,  # , ![x]:A ,  ?[x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(?[y]:(d(y) => ![x]:d(x))).'), nl,
    nl.
% =========================================================================
% END OF DRIVER
% =========================================================================
% =========================================================================
% TRADUCTION DU BICONDITIONNELLE INTERNE
% A <=> B devient (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantifiers: pass recursively into the body
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Propositional connectives
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Base case: atomic formulas
subst_bicond(A, A).

% =========================================================================
% NEGATION SUBSTITUTION (preprocessing)
% =========================================================================
% Double negation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Negation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditional
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Bacis case
subst_neg(A, A).
% =========================================================================
% G4 FOL Prover with equality 
% TPTP-version
% =========================================================================
% prove/7 - 
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
% LogicLevel: minimal | intuitionistic | classical
%==========================================================================
% AXIOMS
%=========================================================================
% O.0 Ax 
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    Delta = [B],
    unify_with_occurs_check(A, B).
% 0.1 L-bot
prove(Gamma>Delta, _, _, SkolemIn, SkolemIn, LogicLevel, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, land(Gamma>Delta,P)) :-
    select((A&B),Gamma,G1), !,
    prove([A,B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L0->  
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, l0cond(Gamma>Delta,P)) :-
    select((A=>B),Gamma,G1),
    member(A,G1), !,
    prove([B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L&->
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, landto(Gamma>Delta,P)) :-
    select(((A&B)=>C),Gamma,G1), !,
    prove([(A=>(B => C))|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],  % Goal: not-A
    % Search in Gamma for a formula with more negations
    member(LongNeg, Gamma),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law). 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), Gamma),  % not-A not already in context
    Threshold > 0,
    prove([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, P).
% 4. Lv-> (OPTIMIZED)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lorto(Gamma>Delta,P)) :-
    select(((A|B)=>C),Gamma,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        prove([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        prove([A=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        prove([B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        prove([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 5. Lv (fallback for all logics including minimal)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lor(Gamma>Delta, P1,P2)) :-
    select((A|B),Gamma,G1), !,
    prove([A|G1]>Delta, FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    prove([B|G1]>Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
% 13. R-forall 
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    J1 is SkolemIn+1,
    prove(Gamma > [A1|D1], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 14. L-forall 
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    length(FreeVars, Len), Len < Threshold,  
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    prove([A1|Gamma] > Delta, [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 8. R-> 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rcond(Gamma>Delta,P)) :-
    Delta = [A=>B], !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 6. L->-> 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ltoto(Gamma>Delta,P1,P2)) :-
    select(((A=>B)=>C),Gamma,G1), !,
    prove([A,(B=>C)|G1]>[B], FreeVars, Threshold, SkolemIn, _J1, LogicLevel, P1),
    prove([C|G1]> Delta, FreeVars, Threshold, _K1, SkolemOut, LogicLevel, P2).
% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    copy_term((X:(A|B),FreeVars), (f_sk(SkolemIn,FreeVars):(A1|B1),FreeVars)),
    J1 is SkolemIn+1,
    prove([A1|G1]>Delta, FreeVars, Threshold, J1, J2, LogicLevel, P1),
    prove([B1|G1]>Delta, FreeVars, Threshold, J2, SkolemOut, LogicLevel, P2).
% 10. R? 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   prove(Gamma>[A], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;   prove(Gamma>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rand(Gamma>Delta,P1,P2)) :-
    Delta = [(A&B)], !,
    prove(Gamma>[A], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    prove(Gamma>[B], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
 % 12. L-exists 
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    J1 is SkolemIn+1,
    prove([A1|G1] > Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 15. R-exists 
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FreeVars, Len), Len < Threshold,  
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    prove(Gamma > [A1|D1], [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 16. CQ_c - Classical rule
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, cq_c(Gamma>Delta,P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    
    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATarget
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        prove([?[ZTarget-YTarget]:ATarget|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ;
        % Otherwise: normal case with X
        prove([?[Z-X]:(A => B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ).
% 17. CQ_m - Minimal rule (minimal and intuitionistic ONLY, last resort)
% IMPORTANT: EXCLUDED from classical logic (IP + standard rules suffice)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, cq_m(Gamma>Delta,P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, Gamma, G1),
    prove([![Z-X]:(A=>B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% =========================================================================
% EQUALITY RULES
% =========================================================================
% REFLEXIVITY: |- t = t
prove(_Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_refl(Delta)) :-
    Delta = [T = T],
    ground(T),
    !.

% SYMMETRY: t = u |- u = t  
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_sym(Gamma>Delta)) :-
    Delta = [A = B],
    member(B = A, Gamma),
    !.

% SIMPLE TRANSITIVITY: t = u, u = v |- t = v
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_trans(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    (   (member(A = B, Gamma), member(B = C, Gamma))
    ;   (member(B = A, Gamma), member(B = C, Gamma))
    ;   (member(A = B, Gamma), member(C = B, Gamma))
    ;   (member(B = A, Gamma), member(C = B, Gamma))
    ),
    !.

% CHAINED TRANSITIVITY: a=b, b=c, c=d |- a=d
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_trans_chain(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    \+ member(A = C, Gamma),
    \+ member(C = A, Gamma),
    find_equality_path(A, C, Gamma, [A], _Path),
    !.

% CONGRUENCE: t = u |- f(t) = f(u)
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_cong(Gamma>Delta)) :-
    Delta = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N),
    length(ArgsR, N),
    N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, Gamma) ; member(TermR = TermL, Gamma)),
    !.

% SUBSTITUTION IN EQUALITY: x=y, f(x)=z |- f(y)=z
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_eq(Gamma>Delta)) :-
    Delta = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, Gamma),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, Gamma),
    X \== Y,
    (
        (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ),
    !.

% SUBSTITUTION (Leibniz): t = u, P(t) |- P(u)
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _),
    Goal \= (_ => _),
    Goal \= (_ & _),
    Goal \= (_ | _),
    Goal \= (!_),
    Goal \= (?_),
    member(A = B, Gamma),
    member(Pred, Gamma),
    Pred \= (_ = _),
    Pred \= (_ => _),
    Pred \= (_ & _),
    Pred \= (_ | _),
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    member_pos(A, Args, Pos),
    nth0(Pos, GoalArgs, B),
    !.

% =========================================================================
% HELPERS
% =========================================================================
% Helper: find position of an element
member_pos(X, [X|_], 0) :- !.
member_pos(X, [_|T], N) :-
    member_pos(X, T, N1),
    N is N1 + 1.

% Helper: substitute Old with New in Term
substitute_in_term(Old, New, Old, New) :- !.
substitute_in_term(Old, New, Term, Result) :-
    compound(Term),
    !,
    Term =.. [F|Args],
    maplist(substitute_in_term(Old, New), Args, NewArgs),
    Result =.. [F|NewArgs].
substitute_in_term(_, _, Term, Term).

% Helper: find position where two lists differ
find_diff_pos([X|_], [Y|_], 0, X, Y) :- X \= Y, !.
find_diff_pos([X|RestL], [X|RestR], Pos, TermL, TermR) :-
    find_diff_pos(RestL, RestR, Pos1, TermL, TermR),
    Pos is Pos1 + 1.

% Helper: find a path (with cycle detection)
find_equality_path(X, X, _, _, [X]) :- !.
find_equality_path(X, Z, Context, Visited, [X|Path]) :-
    (member(X = Y, Context) ; member(Y = X, Context)),
    Y \== X,
    \+ member(Y, Visited),
    find_equality_path(Y, Z, Context, [Y|Visited], Path).

% Helper: verify if Formula = not^n(Target) and return n
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

% =========================================================================
% END of Prover
% =========================================================================
% =========================================================================
% END of Prover
% =========================================================================
% =========================================================================
% G4 PRINTER SPECIALIZED FOR BUSSPROOFS
% Optimized LaTeX rendering for authentic G4 rules
% =========================================================================

% =========================================================================
% G4 rules 
% =========================================================================

% 1. Ax.
render_bussproofs(ax(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$Ax.$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% 2. L0-implies
render_bussproofs(l0cond(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L0\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 3. L-and-implies
render_bussproofs(landto(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\land\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% TNE
render_bussproofs(tne(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 4. L-or-implies
render_bussproofs(lorto(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\lor\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% L-exists-or
render_bussproofs(lex_lor(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\exists\\lor$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 5. L-and
render_bussproofs(land(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\land$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 6. L-or
render_bussproofs(lor(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\lor$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 7. R-implies
render_bussproofs(rcond(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\to$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 8. R-or
render_bussproofs(ror(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\lor$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 9. L-implies-implies
render_bussproofs(ltoto(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$L\\to\\to$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 10. R-and
render_bussproofs(rand(Seq, Proof1, Proof2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof1, VarCounter, Temp1),
    render_bussproofs(Proof2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize{$R\\land$}}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 11. L-bot
render_bussproofs(lbot(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$L\\bot$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% IP : Indirect proof (with DNE_m detection)
render_bussproofs(ip(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    Seq = (_ > [Goal]),
    render_bussproofs(Proof, VarCounter, TempCounter),
    ( Goal = (_ => #) ->
        write('\\RightLabel{\\scriptsize{$DNE_{m}$}}'), nl
    ;
        write('\\RightLabel{\\scriptsize{$IP$}}'), nl
    ),
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
%  FOL QUANTIFICATION RULES
% =========================================================================

% 12. R-forall
render_bussproofs(rall(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\forall$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 13. L-exists
render_bussproofs(lex(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\exists$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 14. R-exists
render_bussproofs(rex(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$R\\exists$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 15. L-forall
render_bussproofs(lall(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$L\\forall$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_c : Classical conversion rule
render_bussproofs(cq_c(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$CQ_{c}$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_m : Minimal conversion rule
render_bussproofs(cq_m(Seq, Proof), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(Proof, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize{$CQ_{m}$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% EQUALITY RULES
% =========================================================================

% Reflexivity : Seq = [t = t]
render_bussproofs(eq_refl(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = I $}}'), nl,
    write('\\UnaryInfC{$'),
    write(' \\vdash '),
    ( Seq = [Goal] -> 
        rewrite(Goal, VarCounter, FinalCounter, GoalLatex),
        write(GoalLatex)
    ;
        render_sequent(Seq, VarCounter, FinalCounter)
    ),
    write('$}'), nl.

% Symmetry
render_bussproofs(eq_sym(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E$}}'),  nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Simple transitivity
render_bussproofs(eq_trans(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E $}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Chained transitivity
render_bussproofs(eq_trans_chain(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Congruence
render_bussproofs(eq_cong(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution in equality
render_bussproofs(eq_subst_eq(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E $}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution (Leibniz)
render_bussproofs(eq_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$ = E$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution for logical equivalence
render_bussproofs(equiv_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize{$\\equiv$}}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% SEQUENT RENDERING
% =========================================================================

% Filter and render sequent
render_sequent(Gamma > Delta, VarCounter, FinalCounter) :-
    % ALWAYS use Gamma from sequent, NOT premiss_list!
    filter_top_from_gamma(Gamma, FilteredGamma),
    
    ( FilteredGamma = [] ->
        % Theorem: no premisses to display
        write(' \\vdash '),
        TempCounter = VarCounter
    ;
        % Sequent with premisses
        render_formula_list(FilteredGamma, VarCounter, TempCounter),
        write(' \\vdash ')
    ),
    ( Delta = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(Delta, TempCounter, FinalCounter)
    ).

% filter_top_from_gamma/2: Remove top (⊤) from premisses list
filter_top_from_gamma([], []).
filter_top_from_gamma([H|T], Filtered) :-
    ( is_top_formula(H) ->
        filter_top_from_gamma(T, Filtered)
    ;
        filter_top_from_gamma(T, RestFiltered),
        Filtered = [H|RestFiltered]
    ).

% is_top_formula/1: Detect if a formula is top (⊤)
% Top is represented as (# => #) or sometimes ~ #
is_top_formula((# => #)) :- !.
is_top_formula(((# => #) => #) => #) :- !.  % Double negation of top
is_top_formula(_) :- fail.

% =========================================================================
% FORMULA LIST RENDERING
% =========================================================================

% Empty list
render_formula_list([], VarCounter, VarCounter) :- !.

% Single formula
render_formula_list([F], VarCounter, FinalCounter) :-
    !,
    rewrite(F, VarCounter, FinalCounter, F_latex),
    write_formula_with_parens(F_latex).

% List of formulas with commas
render_formula_list([F|Rest], VarCounter, FinalCounter) :-
    rewrite(F, VarCounter, TempCounter, F_latex),
    write(F_latex),
    write(', '),
    render_formula_list(Rest, TempCounter, FinalCounter).

% =========================================================================
% INTEGRATION WITH MAIN SYSTEM
% =========================================================================

% Interface compatible with decide/1
render_g4_bussproofs_from_decide(Proof) :-
    render_g4_proof(Proof).

% Interface compatible with prove_formula_clean/3
render_g4_bussproofs_from_clean(Proof) :-
    render_g4_proof(Proof).

% =========================================================================
% COMMENTS AND DOCUMENTATION
% =========================================================================

% This G4 printer is specially optimized for:
% 
% 1. AUTHENTIC G4 RULES:
%    - L0-> (modus ponens G4 signature)
%    - L-and->, L-or-> (curried transformations)
%    - L->-> (special G4 rule)
%    - Exact order from multiprover.pl
%
% 2. MULTI-FORMAT COMPATIBILITY:
%    - Uses rewrite/4 system from latex_utilities.pl
%    - Compatible with FOL quantifiers
%    - Handles anti-sequents for failures
%
% 3. PROFESSIONAL LATEX RENDERING:
%    - Standard bussproofs.sty
%    - Compact and clear labels
%    - Automatic variable counter management
%
% USAGE:
% ?- decide(Formula).  % Automatically uses this printer
% ?- render_g4_proof(Proof).  % Direct proof rendering

% =========================================================================
% END OF G4 PRINTER
% =========================================================================
%========================================================================  
% COMMON ND PRINTING
%========================================================================
% =========================================================================
% CYCLIC TERMS HANDLING
% =========================================================================
make_acyclic_term(Term, Safe) :-
    catch(
        make_acyclic_term(Term, [], _MapOut, Safe),
        _,
        Safe = cyc(Term)
    ).

make_acyclic_term(Term, MapIn, MapOut, Safe) :-
    ( var(Term) ->
        Safe = Term, MapOut = MapIn
    ; atomic(Term) ->
        Safe = Term, MapOut = MapIn
    ; find_pair(Term, MapIn, Value) ->
        Safe = Value, MapOut = MapIn
    ;
        gensym(cyc, Patom),
        Placeholder = cyc(Patom),
        MapMid = [pair(Term, Placeholder)|MapIn],
        Term =.. [F|Args],
        make_acyclic_args(Args, MapMid, MapAfterArgs, SafeArgs),
        SafeTermBuilt =.. [F|SafeArgs],
        replace_pair(Term, Placeholder, SafeTermBuilt, MapAfterArgs, MapOut),
        Safe = SafeTermBuilt
    ).

make_acyclic_args([], Map, Map, []).
make_acyclic_args([A|As], MapIn, MapOut, [SA|SAs]) :-
    make_acyclic_term(A, MapIn, MapMid, SA),
    make_acyclic_args(As, MapMid, MapOut, SAs).

find_pair(Term, [pair(Orig,Val)|_], Val) :- Orig == Term, !.
find_pair(Term, [_|Rest], Val) :- find_pair(Term, Rest, Val).

replace_pair(Term, OldVal, NewVal, [pair(Orig,OldVal)|Rest], [pair(Orig,NewVal)|Rest]) :- 
    Orig == Term, !.
replace_pair(Term, OldVal, NewVal, [H|T], [H|T2]) :- 
    replace_pair(Term, OldVal, NewVal, T, T2).
replace_pair(_, _, _, [], []).

% =========================================================================
% HELPER COMBINATORS
% =========================================================================

% Helper: Remove ALL annotations (not just quantifiers)
strip_annotations_deep(@(Term, _), Stripped) :- 
    !, strip_annotations_deep(Term, Stripped).
strip_annotations_deep(![_-X]:Body, ![X]:StrippedBody) :- 
    !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(?[_-X]:Body, ?[X]:StrippedBody) :- 
    !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(A & B, SA & SB) :- 
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A | B, SA | SB) :- 
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A => B, SA => SB) :- 
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A <=> B, SA <=> SB) :- 
    !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(Term, Term).

% =========================================================================
% FITCH DERIVATION HELPERS
% =========================================================================

derive_and_continue(Scope, Formula, RuleTemplate, Refs, RuleTerm, SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, DerivLine, _, VarIn, V1),
    fitch_g4_proof(SubProof, [DerivLine:Formula|Context], Scope, DerivLine, NextLine, ResLine, V1, VarOut).

derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    NextLine is CurLine + 1,
    assert_safe_fitch_line(NextLine, Formula, RuleTerm, Scope),
    format(atom(Just), RuleTemplate, Refs),
    render_have(Scope, Formula, Just, CurLine, NextLine, VarIn, VarOut),
    ResLine = NextLine.

assume_in_scope(Assumption, _Goal, SubProof, Context, ParentScope, StartLine, EndLine, GoalLine, VarIn, VarOut) :-
    AssLine is StartLine + 1,
    assert_safe_fitch_line(AssLine, Assumption, assumption, ParentScope),
    render_hypo(ParentScope, Assumption, 'AS', StartLine, AssLine, VarIn, V1),
    NewScope is ParentScope + 1,
    fitch_g4_proof(SubProof, [AssLine:Assumption|Context], NewScope, AssLine, EndLine, GoalLine, V1, VarOut).

% =========================================================================
% FORMULA EXTRACTION & HELPERS
% =========================================================================

extract_new_formula(CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ member(NewFormula, CurrentPremisses),
    !.
extract_new_formula(_CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ is_quantified(NewFormula),
    !.
extract_new_formula(CurrentPremisses, SubProof, _) :-
    format('% ERROR extract_new_formula: No suitable formula found~n', []),
    format('%   CurrentPremisses: ~w~n', [CurrentPremisses]),
    SubProof =.. [Rule|[(SubPremisses > _)|_]],
    format('%   SubProof rule: ~w~n', [Rule]),
    format('%   SubPremisses: ~w~n', [SubPremisses]),
    fail.

% =========================================================================
% FIND_CONTEXT_LINE: Match formulas in context
% =========================================================================
% ABSOLUTE PRIORITY: PREMISSES (lines 1-N where N = number of premisses)
% =========================================================================

find_context_line(Formula, Context, LineNumber) :-
    premiss_list(PremList),
    length(PremList, NumPremisses),
    % Search ONLY in the first N lines
    member(LineNumber:ContextFormula, Context),
    LineNumber =< NumPremisses,
    % Match with different possible variants
    ( ContextFormula = Formula
    ; strip_annotations_match(Formula, ContextFormula)
    ; formulas_equivalent(Formula, ContextFormula)
    ),
    !.  % Cut as soon as found in premisses

% =========================================================================
% PRIORITY -1: QUANTIFIER NEGATION (original ~ form)
% =========================================================================

% Search for (![x-x]:Body) => # but context has ~![x]:Body (original form)
find_context_line((![_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Original form with ~
        ContextFormula = (~ ![_]:Body)
    ;
        % Transformed form
        ContextFormula = ((![_]:Body) => #)
    ;
        % Transformed form with annotation
        ContextFormula = ((![_-_]:Body) => #)
    ),
    !.

% Same for existential
find_context_line((?[_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (~ ?[_]:Body)
    ;
        ContextFormula = ((?[_]:Body) => #)
    ;
        ContextFormula = ((?[_-_]:Body) => #)
    ),
    !.

% =========================================================================
% PRIORITY 0: QUANTIFIERS - MATCH COMPLEX INTERNAL STRUCTURE
% =========================================================================

% Universal: match internal structure independently of transformation
find_context_line(![Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Case 1: Context without annotation
        ContextFormula = (![Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        % Case 2: Context with annotation
        ContextFormula = (![Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% Existential: match internal structure
find_context_line(?[Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        ContextFormula = (?[Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITY 1: NEGATIONS (original ~ notation vs transformed => #)
% -------------------------------------------------------------------------

% Case 1: Search for ?[x]:A => # but context has ~ ?[x]:A
find_context_line((?[Z-_]:A) => #, Context, LineNumber) :-
    member(LineNumber:(~ ?[Z]:A), Context), !.

% Case 2: Search for ![x]:(A => #) but context has ![x]: ~A
find_context_line(![Z-_]:(A => #), Context, LineNumber) :-
    member(LineNumber:(![Z]: ~A), Context), !.

% Case 3: Search for A => # but context has ~A (simple formula)
find_context_line(A => #, Context, LineNumber) :-
    A \= (?[_]:_),
    A \= (![_]:_),
    member(LineNumber:(~A), Context), !.

% -------------------------------------------------------------------------
% PRIORITY 2: QUANTIFIERS (with/without variable annotations)
% -------------------------------------------------------------------------

% Universal: search for ![x-x]:Body but context has ![x]:Body
find_context_line(![Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (![Z]:Body)      % Without annotation
    ;
        ContextFormula = (![Z-_]:Body)    % With different annotation
    ),
    !.

% Existential: search for ?[x-x]:Body but context has ?[x]:Body
find_context_line(?[Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:Body)      % Without annotation
    ;
        ContextFormula = (?[Z-_]:Body)    % With different annotation
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITY 3: BICONDITIONALS (decomposed)
% -------------------------------------------------------------------------

find_context_line((A => B) & (B => A), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

find_context_line((B => A) & (A => B), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

% -------------------------------------------------------------------------
% PRIORITY 4: EXACT MATCH
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:Formula, Context), !.

% -------------------------------------------------------------------------
% PRIORITY 5: UNIFICATION
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    unify_with_occurs_check(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% PRIORITY 6: STRUCTURE MATCHING
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    match_formula_structure(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% FALLBACK: WARNING if no match found
% -------------------------------------------------------------------------

find_context_line(Formula, _Context, 0) :-
    format('% WARNING: Formula ~w not found in context~n', [Formula]).

% =========================================================================
% HELPER: Formula equivalence (pure structural comparison)
% =========================================================================

% Helper: match by removing annotations
strip_annotations_match(![_-X]:Body, ![X]:Body) :- !.
strip_annotations_match(![X]:Body, ![_-X]:Body) :- !.
strip_annotations_match(?[_-X]:Body, ?[X]:Body) :- !.
strip_annotations_match(?[X]:Body, ?[_-X]:Body) :- !.
strip_annotations_match(A, B) :- A = B.

% Biconditional: match structure without considering order
formulas_equivalent((A1 => B1) & (B2 => A2), C <=> D) :- 
    !,
    (
        (formulas_equivalent(A1, C), formulas_equivalent(A2, C),
         formulas_equivalent(B1, D), formulas_equivalent(B2, D))
    ;
        (formulas_equivalent(A1, D), formulas_equivalent(A2, D),
         formulas_equivalent(B1, C), formulas_equivalent(B2, C))
    ).

formulas_equivalent(A <=> B, (C => D) & (D2 => C2)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(A, C2),
         formulas_equivalent(B, D), formulas_equivalent(B, D2))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(A, D2),
         formulas_equivalent(B, C), formulas_equivalent(B, C2))
    ).

formulas_equivalent((A <=> B), (C <=> D)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(B, D))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(B, C))
    ).

% Transformed negation
formulas_equivalent(A => #, ~ B) :- !, formulas_equivalent(A, B).
formulas_equivalent(~ A, B => #) :- !, formulas_equivalent(A, B).

% Quantifiers: compare bodies only (ignore variable)
formulas_equivalent(![_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

formulas_equivalent(?[_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

% Binary connectives
formulas_equivalent(A & B, C & D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A | B, C | D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A => B, C => D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).

% Bottom
formulas_equivalent(#, #) :- !.

% Predicates/Terms: compare structure (ignore variables)
formulas_equivalent(Term1, Term2) :-
    compound(Term1),
    compound(Term2),
    !,
    Term1 =.. [Functor|_Args1],
    Term2 =.. [Functor|_Args2],
    % Same functor is sufficient (we ignore arguments that are variables)
    !.

% Strict identity
formulas_equivalent(A, B) :- A == B, !.

% Fallback: atomic terms with same name
formulas_equivalent(A, B) :- 
    atomic(A), atomic(B),
    !.

% Helper: match two formulas by structure (modulo variable renaming)

% Negations
match_formula_structure(A => #, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~A, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(A => #, ~ B) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~ A, ~ B) :- 
    !, match_formula_structure(A, B).

% Quantifiers
match_formula_structure(![_-_]:Body1, ![_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).
match_formula_structure(?[_-_]:Body1, ?[_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).

% Binary connectives
match_formula_structure(A & B, C & D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A | B, C | D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A => B, C => D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A <=> B, C <=> D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).

% Bottom
match_formula_structure(#, #) :- !.

% Strict equality
match_formula_structure(A, B) :-
    A == B, !.

% Subsumption
match_formula_structure(A, B) :-
    subsumes_term(A, B) ; subsumes_term(B, A).

% =========================================================================
% ADDITIONAL FITCH HELPERS
% =========================================================================

find_disj_context(L, R, Context, Line) :-
    ( member(Line:(CL | CR), Context), subsumes_term((L | R), (CL | CR)) -> true
    ; member(Line:(CL | CR), Context), \+ \+ ((L = CL, R = CR))
    ).

extract_witness(SubProof, Witness) :-
    SubProof =.. [Rule|Args],
    Args = [(Prem > _)|_],
    ( member(Witness, Prem), contains_skolem(Witness), 
      ( Rule = rall ; Rule = lall ; \+ is_quantified(Witness) ) 
    ), !.
extract_witness(SubProof, Witness) :-
    SubProof =.. [_, (_ > _), SubSP|_],
    extract_witness(SubSP, Witness).

is_quantified(![_-_]:_) :- !.
is_quantified(?[_-_]:_) :- !.

contains_skolem(Formula) :-
    Formula =.. [_|Args],
    member(Arg, Args),
    (Arg = f_sk(_,_) ; compound(Arg), contains_skolem(Arg)).

is_direct_conjunct(G, (A & B)) :- (G = A ; G = B), !.
is_direct_conjunct(G, (A & R)) :- (G = A ; is_direct_conjunct(G, R)).

extract_conjuncts((A & B), CLine, Scope, CurLine, [L1:A, L2:B], L2, VarIn, VarOut) :-
    L1 is CurLine + 1,
    L2 is CurLine + 2,
    assert_safe_fitch_line(L1, A, land(CLine), Scope),
    assert_safe_fitch_line(L2, B, land(CLine), Scope),
    format(atom(Just1), '$ \\land E $ ~w', [CLine]),
    format(atom(Just2), '$ \\land E $ ~w', [CLine]),
    render_have(Scope, A, Just1, CurLine, L1, VarIn, V1),
    render_have(Scope, B, Just2, L1, L2, V1, VarOut).

% =========================================================================
% IMMEDIATE DERIVATION LOGIC
% =========================================================================

derive_immediate(Scope, Formula, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Formula, RuleTerm, Scope),
    format(atom(Just), JustFormat, JustArgs),
    render_have(Scope, Formula, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

try_derive_immediately(Goal, Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ResLine:Goal, Context),
    !,
    NextLine = CurLine,
    VarOut = VarIn.

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(MajLine:(Ant => Goal), Context),
    member(MinLine:Ant, Context),
    !,
    RuleTerm = l0cond(MajLine, MinLine),
    JustFormat = '$ \\to E $ ~w,~w',
    JustArgs = [MajLine, MinLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ConjLine:(A & B), Context),
    (Goal = A ; Goal = B),
    !,
    RuleTerm = land(ConjLine),
    JustFormat = '$ \\land E $ ~w',
    JustArgs = [ConjLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(FLine: #, Context),
    !,
    RuleTerm = lbot(FLine),
    JustFormat = '$ \\bot E $ ~w',
    JustArgs = [FLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L | R),
    ( member(SLine:L, Context) -> true ; member(SLine:R, Context) ),
    !,
    RuleTerm = ror(SLine),
    JustFormat = '$ \\lor I $ ~w',
    JustArgs = [SLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L & R),
    member(LLine:L, Context),
    member(RLine:R, Context),
    !,
    RuleTerm = rand(LLine, RLine),
    JustFormat = '$ \\land I $ ~w,~w',
    JustArgs = [LLine, RLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% SHARED HYPOTHESIS MAP CONSTRUCTION
% =========================================================================

build_hypothesis_map([], Map, Map).
build_hypothesis_map([N-Formula-assumption-Scope|Rest], AccMap, FinalMap) :-
    !,
    ( member(M-Formula-assumption-Scope, Rest), M > N ->
        build_hypothesis_map(Rest, [M-N|AccMap], FinalMap)
    ;
        build_hypothesis_map(Rest, AccMap, FinalMap)
    ).
build_hypothesis_map([_|Rest], AccMap, FinalMap) :-
    build_hypothesis_map(Rest, AccMap, FinalMap).

% =========================================================================
% End of common ND PRINTING
% =========================================================================

% =========================================================================
% NATURAL DEDUCTION PRINTER IN FLAG STYLE  
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic abbreviated_line/1.

% =========================================================================
% FROM G4 Sequent Calculus To Natural Deduction in Fitch Style 
% =========================================================================

g4_to_fitch_sequent(Proof, OriginalSequent) :-
    !,
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    
    OriginalSequent = (_Gamma > [Conclusion]),
    
    ( premiss_list(PremList), PremList \= [] ->
        render_premiss_list(PremList, 0, 1, NextLine, InitialContext),
        LastPremLine is NextLine - 1  % CORRECTION: last premiss line
    ;
        _NextLine = 1,
        LastPremLine = 0,             % CORRECTION: no premisses
        InitialContext = []
    ),
    
    % CORRECTION: Scope=1 (indentation), CurLine=LastPremLine (numbering)
    fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _),
    
    % DETECT: Has any rule been applied?
    ( LastLine = LastPremLine ->
        % No line added -> pure axiom -> display reiteration
        NewLine is LastPremLine + 1,
        assert_safe_fitch_line(NewLine, Conclusion, reiteration(ResLine), 0),
        write('\\fa '),
        rewrite(Conclusion, 0, _, LatexConclusion),
        write(LatexConclusion),
        format(' &  R ~w\\\\', [ResLine]), nl
    ;
        % A rule has already displayed the conclusion -> do nothing
        true
    ).

% g4_to_fitch_theorem/1: For theorems (original behavior)
g4_to_fitch_theorem(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _).

% =========================================================================
% PREMISS DISPLAY
% =========================================================================

% render_premiss_list/5: Display a list of premisses in Fitch style
render_premiss_list([], _, Line, Line, []) :- !.

render_premiss_list([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    render_fitch_indent(Scope),
    write(' \\fj '),
    rewrite(LastPremiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, LastPremiss, premiss, Scope),
    NextLine is CurLine + 1.
    
render_premiss_list([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    render_fitch_indent(Scope),
    write(' \\fa '),
    rewrite(Premiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, Premiss, premiss, Scope),
    NextCurLine is CurLine + 1,
    render_premiss_list(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% SAFE ASSERTION
% =========================================================================

assert_safe_fitch_line(N, Formula, Just, Scope) :-
    catch(
        (
            ( acyclic_term(Formula) ->
                Safe = Formula
            ;
                make_acyclic_term(Formula, Safe)
            ),
            assertz(fitch_line(N, Safe, Just, Scope))
        ),
        Error,
        (
            format('% Warning: Could not assert line ~w: ~w~n', [N, Error]),
            assertz(fitch_line(N, error_term(Formula), Just, Scope))
        )
    ).

% =========================================================================
% @ SUBSTITUTION HANDLING
% =========================================================================

fitch_g4_proof(@(ProofTerm, _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    fitch_g4_proof(ProofTerm, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% AXIOM
% =========================================================================

fitch_g4_proof(ax((Premisses > [Goal]), _Tag), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

fitch_g4_proof(ax((Premisses > [Goal])), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

% =========================================================================
% PROPOSITIONAL RULES 
% =========================================================================

% L0-implies
fitch_g4_proof(l0cond((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    select((Ant => Cons), Premisses, Remaining),
    member(Ant, Remaining),
    find_context_line((Ant => Cons), Context, MajLine),
    find_context_line(Ant, Context, MinLine),
    DerLine is CurLine + 1,
    format(atom(Just), '$ \\to E $ ~w,~w', [MajLine, MinLine]),
    render_have(Scope, Cons, Just, CurLine, DerLine, VarIn, V1),
    assert_safe_fitch_line(DerLine, Cons, l0cond(MajLine, MinLine), Scope),
    fitch_g4_proof(SubProof, [DerLine:Cons|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut).

% L-and-implies
fitch_g4_proof(landto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select(((A & B) => C), Premisses, _),
    find_context_line(((A & B) => C), Context, ImpLine),
    derive_and_continue(Scope, NewFormula, '$ \\land\\to E $ ~w', [ImpLine],
                       landto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% L-or-implies: Disjunction to implications
fitch_g4_proof(lorto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    findall(F, (member(F, SubPremisses), \+ member(F, Premisses)), NewFormulas),
    select(((A | B) => C), Premisses, _),
    find_context_line(((A | B) => C), Context, ImpLine),
    ( NewFormulas = [F1, F2] ->
        Line1 is CurLine + 1,
        Line2 is CurLine + 2,
        assert_safe_fitch_line(Line1, F1, lorto(ImpLine), Scope),
        assert_safe_fitch_line(Line2, F2, lorto(ImpLine), Scope),
        format(atom(Just), '$ \\lor\\to E $ ~w', [ImpLine]),
        render_have(Scope, F1, Just, CurLine, Line1, VarIn, V1),
        render_have(Scope, F2, Just, Line1, Line2, V1, V2),
        fitch_g4_proof(SubProof, [Line2:F2, Line1:F1|Context], Scope, Line2, NextLine, ResLine, V2, VarOut)
    ; NewFormulas = [F1] ->
        derive_and_continue(Scope, F1, '$ \\lor\\to E $ ~w', [ImpLine],
                           lorto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ).

% L-and: Conjunction elimination
fitch_g4_proof(land((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((A & B), Premisses, _),
    find_context_line((A & B), Context, ConjLine),
    ( is_direct_conjunct(Goal, (A & B)) ->
        derive_formula(Scope, Goal, '$ \\land E $ ~w', [ConjLine], land(ConjLine),
                      CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        extract_conjuncts((A & B), ConjLine, Scope, CurLine, ExtCtx, LastLine, VarIn, V1),
        append(ExtCtx, Context, NewCtx),
        fitch_g4_proof(SubProof, NewCtx, Scope, LastLine, NextLine, ResLine, V1, VarOut)
    ).

% L-bot: Explosion
fitch_g4_proof(lbot((Premisses > [Goal]), _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(#, Premisses),
    member(FalseLine: #, Context),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, lbot(FalseLine), Scope),
    format(atom(Just), '$ \\bot E $ ~w', [FalseLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% R-or: Disjunction introduction
fitch_g4_proof(ror((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (_ | _), try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
        true
    ; fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, DisjunctLine, VarIn, V1),
      OrLine is SubEnd + 1,
      assert_safe_fitch_line(OrLine, Goal, ror(DisjunctLine), Scope),
      format(atom(Just), '$ \\lor I $ ~w', [DisjunctLine]),
      render_have(Scope, Goal, Just, SubEnd, OrLine, V1, VarOut),
      NextLine = OrLine,
      ResLine = OrLine
    ).

% =========================================================================
% RULES WITH HYPOTHESES (ASSUME-DISCHARGE)
% =========================================================================

% R-implies: Implication introduction
fitch_g4_proof(rcond((_ > [A => B]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% TNE: Triple negation elimination
fitch_g4_proof(tne((_ > [(A => B)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% IP: Indirect proof / Classical
fitch_g4_proof(ip((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (A => #) ->
        Assumption = ((A => #) => #),
        Rule = 'DNE_m'
    ;
        Assumption = (Goal => #),
        Rule = 'IP'
    ),
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, Assumption, assumption, Scope),
    render_hypo(Scope, Assumption, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:Assumption|Context], NewScope, HypLine, SubEnd, BotLine, V1, V2),
    IPLine is SubEnd + 1,
    assert_safe_fitch_line(IPLine, Goal, ip(HypLine, BotLine), Scope),
    format(atom(Just), '~w ~w-~w', [Rule, HypLine, BotLine]),
    render_have(Scope, Goal, Just, SubEnd, IPLine, V2, VarOut),
    NextLine = IPLine,
    ResLine = IPLine.

% L-or: Disjunction elimination
fitch_g4_proof(lor((Premisses > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
       true
    ; 
      select((A | B), Premisses, _),
      % First try to find the disjunction in the context, otherwise in premisses
      ( find_disj_context(A, B, Context, DisjLine) ->
          true
      ;
          % Disjunction is a premiss, find its line
          find_context_line((A | B), Context, DisjLine)
      ),
      AssLineA is CurLine + 1,
      assert_safe_fitch_line(AssLineA, A, assumption, Scope),
      render_hypo(Scope, A, 'AS', CurLine, AssLineA, VarIn, V1),
      NewScope is Scope + 1,
      fitch_g4_proof(SP1, [AssLineA:A|Context], NewScope, AssLineA, EndA, GoalA, V1, V2),
      AssLineB is EndA + 1,
      assert_safe_fitch_line(AssLineB, B, assumption, Scope),
      render_hypo(Scope, B, 'AS', EndA, AssLineB, V2, V3),
      fitch_g4_proof(SP2, [AssLineB:B|Context], NewScope, AssLineB, EndB, GoalB, V3, V4),
      ElimLine is EndB + 1,
      assert_safe_fitch_line(ElimLine, Goal, lor(DisjLine, AssLineA, AssLineB, GoalA, GoalB), Scope),
      format(atom(Just), '$ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, AssLineA, GoalA, AssLineB, GoalB]),
      render_have(Scope, Goal, Just, EndB, ElimLine, V4, VarOut),
      NextLine = ElimLine,
      ResLine = ElimLine
    ).

% =========================================================================
% BINARY RULES
% =========================================================================

% R-and: Conjunction introduction
fitch_g4_proof(rand((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    Goal = (L & _R),
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) -> true
    ; fitch_g4_proof(SP1, Context, Scope, CurLine, End1, LeftLine, VarIn, V1),
      fitch_g4_proof(SP2, [LeftLine:L|Context], Scope, End1, End2, RightLine, V1, V2),
      derive_formula(Scope, Goal, '$ \\land I $ ~w,~w', [LeftLine, RightLine], rand(LeftLine, RightLine),
                    End2, NextLine, ResLine, V2, VarOut)
    ).

% L-implies-implies: Special G4 rule
fitch_g4_proof(ltoto((Premisses > _), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select(((Ant => Inter) => Cons), Premisses, _),
    find_context_line(((Ant => Inter) => Cons), Context, ComplexLine),
    
    % STEP 1: Derive (Inter => Cons) by L->->
    ExtractLine is CurLine + 1,
    format(atom(ExtractJust), '$ \\to\\to E$ ~w', [ComplexLine]),
    render_have(Scope, (Inter => Cons), ExtractJust, CurLine, ExtractLine, VarIn, V1),
    assert_safe_fitch_line(ExtractLine, (Inter => Cons), ltoto(ComplexLine), Scope),
    
    % STEP 2: Assume Ant
    AssLine is ExtractLine + 1,
    assert_safe_fitch_line(AssLine, Ant, assumption, Scope),
    render_hypo(Scope, Ant, 'AS', ExtractLine, AssLine, V1, V2),
    NewScope is Scope + 1,
    
    % STEP 3: Prove Inter with [Ant, (Inter=>Cons) | Context]
    fitch_g4_proof(SP1, [AssLine:Ant, ExtractLine:(Inter => Cons)|Context],
                  NewScope, AssLine, SubEnd, InterLine, V2, V3),
    
    % STEP 4: Derive (Ant => Inter) by ->I
    ImpLine is SubEnd + 1,
    assert_safe_fitch_line(ImpLine, (Ant => Inter), rcond(AssLine, InterLine), Scope),
    format(atom(Just1), '$ \\to I $ ~w-~w', [AssLine, InterLine]),
    render_have(Scope, (Ant => Inter), Just1, SubEnd, ImpLine, V3, V4),
    
    % STEP 5: Derive Cons by ->E
    MPLine is ImpLine + 1,
    assert_safe_fitch_line(MPLine, Cons, l0cond(ComplexLine, ImpLine), Scope),
    format(atom(Just2), '$ \\to E $ ~w,~w', [ComplexLine, ImpLine]),
    render_have(Scope, Cons, Just2, ImpLine, MPLine, V4, V5),
    
    % STEP 6: Continue with SP2
    fitch_g4_proof(SP2, [MPLine:Cons, ImpLine:(Ant => Inter), ExtractLine:(Inter => Cons)|Context],
                  Scope, MPLine, NextLine, ResLine, V5, VarOut).

% =========================================================================
% QUANTIFICATION RULES
% =========================================================================

% R-forall
fitch_g4_proof(rall((_ > [(![Z-X]:A)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, BodyLine, VarIn, V1),
    derive_formula(Scope, (![Z-X]:A), '$ \\forall I $ ~w', [BodyLine], rall(BodyLine),
                  SubEnd, NextLine, ResLine, V1, VarOut).

% L-forall: Universal elimination
fitch_g4_proof(lall((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses > _, SubProof, NewFormula),
    
    % Find the universal quantifier that generates NewFormula
    (
        % Case 1: NewFormula is a direct instance of a universal in Premisses
        (
            member((![Z-X]:Body), Premisses),
            % Check if Body (with substitution) gives NewFormula
            strip_annotations_deep(Body, StrippedBody),
            strip_annotations_deep(NewFormula, StrippedNew),
            unifiable(StrippedBody, StrippedNew, _),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 2: Search by equivalent structure
            member((![Z-X]:Body), Premisses),
            formulas_equivalent(Body, NewFormula),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 3: Fallback - take the first (current behavior)
            select((![Z-X]:Body), Premisses, _),
            UniversalFormula = (![Z-X]:Body)
        )
    ),
    
    find_context_line(UniversalFormula, Context, UnivLine),
    derive_and_continue(Scope, NewFormula, '$ \\forall E $ ~w', [UnivLine], lall(UnivLine),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% R-exists
fitch_g4_proof(rex((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, _WitnessLine, VarIn, V1),
    % CORRECTION: Reference SubEnd (witness line), not WitnessLine
    derive_formula(Scope, Goal, '$ \\exists I $ ~w', [SubEnd], rex(SubEnd),
                  SubEnd, NextLine, ResLine, V1, VarOut).

% L-exists
fitch_g4_proof(lex((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),
    extract_witness(SubProof, Witness),
    ( member(_:Witness, Context) ->
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ; WitLine is CurLine + 1,
      NewScope is Scope + 1,
      assert_safe_fitch_line(WitLine, Witness, assumption, NewScope),
      render_hypo(Scope, Witness, 'AS', CurLine, WitLine, VarIn, V1),
      fitch_g4_proof(SubProof, [WitLine:Witness|Context], NewScope, WitLine, SubEnd, _GoalLine, V1, V2),
      ElimLine is SubEnd + 1,
      assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, SubEnd), Scope),
      % CORRECTION: Reference SubEnd (last line of subproof)
      format(atom(Just), '$ \\exists E $ ~w,~w-~w', [ExistLine, WitLine, SubEnd]),
      render_have(Scope, Goal, Just, SubEnd, ElimLine, V2, VarOut),
      NextLine = ElimLine, ResLine = ElimLine
    ).

% L-exists-or: Combined existential-disjunction 
fitch_g4_proof(lex_lor((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SP1 =.. [_, (Prem1 > _)|_],
    SP2 =.. [_, (Prem2 > _)|_],
    member(WitA, Prem1), contains_skolem(WitA), \+ is_quantified(WitA),
    member(WitB, Prem2), contains_skolem(WitB), \+ is_quantified(WitB),
    WitLine is CurLine + 1,
    render_hypo(Scope, (WitA | WitB), 'AS', CurLine, WitLine, VarIn, V1),
    NewScope is Scope + 1,
    assume_in_scope(WitA, Goal, SP1, [WitLine:(WitA | WitB)|Context],
                   NewScope, WitLine, EndA, GoalA, V1, V2),
    assume_in_scope(WitB, Goal, SP2, [WitLine:(WitA | WitB)|Context],
                   NewScope, EndA, EndB, GoalB, V2, V3),
    DisjElim is EndB + 1,
    CaseAStart is WitLine + 1,
    CaseBStart is EndA + 1,
    format(atom(DisjJust), '$ \\lor E $ ~w,~w-~w,~w-~w',
           [WitLine, CaseAStart, GoalA, CaseBStart, GoalB]),
    render_have(NewScope, Goal, DisjJust, EndB, DisjElim, V3, V4),
    ElimLine is DisjElim + 1,
    format(atom(ExistJust), '$ \\exists E $ ~w-~w', [WitLine, DisjElim]),
    render_have(Scope, Goal, ExistJust, DisjElim, ElimLine, V4, VarOut),
    NextLine = ElimLine, ResLine = ElimLine.

% CQ_c: Classical quantifier conversion
fitch_g4_proof(cq_c((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((![Z-X]:A) => B, Premisses, _),
    find_context_line((![Z-X]:A) => B, Context, Line),
    derive_and_continue(Scope, NewFormula, '$ CQ_{c} $ ~w', [Line], cq_c(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% CQ_m: Minimal quantifier conversion
fitch_g4_proof(cq_m((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((?[Z-X]:A)=>B, Premisses, _),
    find_context_line((?[Z-X]:A)=>B, Context, Line),
    derive_and_continue(Scope, NewFormula, '$ CQ_{m} $ ~w', [Line], cq_m(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% EQUALITY RULES
% =========================================================================

% Reflexivity
fitch_g4_proof(eq_refl(Delta), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_refl, Scope),
    render_have(Scope, Goal, '$ = I$', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Symmetry
fitch_g4_proof(eq_sym(_Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = B],
    find_context_line(B = A, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = B), eq_sym(EqLine), Scope),
    format(atom(Just), '$ = E $ ~w', [EqLine]),
    render_have(Scope, (A = B), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivity
fitch_g4_proof(eq_trans(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = C],
    Gamma = [A = B, B = C | _Rest],  % Direct pattern matching
    find_context_line(A = B, Context, Line1),
    find_context_line(B = C, Context, Line2),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans(Line1, Line2), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [Line1, Line2]),
    render_have(Scope, (A = C), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution (Leibniz) - MAIN CASE
fitch_g4_proof(eq_subst(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal],
    Goal \= (_ = _),  % Not an equality
    
    % Extract equality and predicate from Gamma
    member(A = B, Gamma),
    member(Pred, Gamma),
    Pred \= (_ = _),
    Pred \= (A = B),
    
    % Verify that Goal is Pred with A replaced by B
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    
    % Find position where substitution occurs
    nth0(Pos, Args, A),
    nth0(Pos, GoalArgs, B),
    
    % Find line numbers in context
    find_context_line(A = B, Context, EqLine),
    find_context_line(Pred, Context, PredLine),
    
    !,
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_subst(EqLine, PredLine), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [EqLine, PredLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Congruence
fitch_g4_proof(eq_cong(_Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    find_context_line(TermL = TermR, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (LHS = RHS), eq_cong(EqLine), Scope),
    format(atom(Just), '$ = E$ ~w', [EqLine]),
    render_have(Scope, (LHS = RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution in equality
fitch_g4_proof(eq_subst_eq(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal_LHS = Goal_RHS],
    member(X = Y, Gamma),
    member(Ctx_LHS = Ctx_RHS, Gamma),
    find_context_line(X = Y, Context, XY_Line),
    find_context_line(Ctx_LHS = Ctx_RHS, Context, Ctx_Line),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (Goal_LHS = Goal_RHS), eq_subst_eq(XY_Line, Ctx_Line), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [XY_Line, Ctx_Line]),
    render_have(Scope, (Goal_LHS = Goal_RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Chained transitivity
fitch_g4_proof(eq_trans_chain(_Gamma>Delta), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = C],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans_chain, Scope),
    render_have(Scope, (A = C), '=E', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% =========================================================================
% FALLBACK
% =========================================================================

fitch_g4_proof(UnknownRule, _Context, _Scope, CurLine, CurLine, CurLine, VarIn, VarIn) :-
    format('% WARNING: Unknown rule ~w~n', [UnknownRule]).

% =========================================================================
%  END OF FITCH PRINTER 
% =========================================================================
% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE  
% =========================================================================
% =========================================================================
% DISPLAY PREMISS LIST FOR TREE STYLE 
% =========================================================================
% render_premiss_list_silent/5: Silent version for tree style
render_premiss_list_silent([], _, Line, Line, []) :- !.

render_premiss_list_silent([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    assert_safe_fitch_line(CurLine, LastPremiss, premiss, Scope),
    NextLine is CurLine + 1.

render_premiss_list_silent([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    assert_safe_fitch_line(CurLine, Premiss, premiss, Scope),
    NextCurLine is CurLine + 1,
    render_premiss_list_silent(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% TREE STYLE INTERFACE
% =========================================================================
render_nd_tree_proof(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    extract_formula_from_proof(Proof, TopFormula),
    detect_and_set_logic_level(TopFormula),
    catch(
        (
            ( premiss_list(PremissList), PremissList = [_|_] ->
                render_premiss_list_silent(PremissList, 0, 1, NextLine, InitialContext),
                LastPremLine is NextLine - 1,
                % Capture ResLine (6th argument) and LastLine (5th) which is the conclusion line
                with_output_to(atom(_), fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _)),
                % If no line was added (pure axiom), add reiteration line
                ( LastLine = LastPremLine ->
                    NewLine is LastPremLine + 1,
                    fitch_line(ResLine, Conclusion, _, _),
                    assert_safe_fitch_line(NewLine, Conclusion, reiteration(ResLine), 0),
                    RootLine = NewLine
                ;
                    RootLine = ResLine
                )
            ;
                % No premisses
                with_output_to(atom(_), fitch_g4_proof(Proof, [], 1, 0, _, ResLine, 0, _)),
                RootLine = ResLine
            ),
            % Use RootLine as the root of the tree
            collect_and_render_tree(RootLine)
        ),
        Error,
        (
            format('% Error rendering ND tree: ~w~n', [Error]),
            write('% Skipping tree visualization'), nl
        )
    ).

% =========================================================================
% COLLECT AND RENDER TREE
% =========================================================================

collect_and_render_tree(RootLineNum) :-
    findall(N-Formula-Just-Scope, 
            (fitch_line(N, Formula, Just, Scope), \+ abbreviated_line(N)), 
            Lines),
    predsort(compare_lines, Lines, SortedLines),
    ( SortedLines = [] ->
        write('% Empty proof tree'), nl
    ;
        % Collect all premiss formulas for conditional wrapping
        findall(F, fitch_line(_, F, premiss, _), AllPremisses),

        ( build_buss_tree(RootLineNum, SortedLines, Tree) ->
            
            % Check if the conclusion is simple (premiss/reiteration) AND there are multiple premisses
            % FIX: Check RootLineNum for justification, not just any line.
            ( is_simple_conclusion(RootLineNum, AllPremisses) ->
                % Force structure to display ALL premisses as branches
                wrap_premisses_in_tree(RootLineNum, AllPremisses, FinalTree)
            ;
                FinalTree = Tree
            ),
            
            write('\\begin{prooftree}'), nl,
            render_buss_tree(FinalTree),
            write('\\end{prooftree}'), nl
        ;
            write('% Warning: missing referenced line(s) or broken tree structure'), nl
        )
    ).

compare_lines(Delta, N1-_-_-_, N2-_-_-_) :-
    compare(Delta, N1, N2).

% Helper to check if conclusion is a simple reiteration or premiss
% FIX: Ensures the justification check is for the RootLineNum.
is_simple_conclusion(RootLineNum, AllPremisses) :-
    length(AllPremisses, N),
    N > 1, % Must have multiple premisses
    fitch_line(RootLineNum, _, Just, _), % Check RootLineNum's justification
    ( Just = premiss ; Just = reiteration(_) ),
    !.

% Helper to force creation of n-ary premiss node
wrap_premisses_in_tree(RootLineNum, AllPremisses, FinalTree) :-
    % Create a list of premiss_node(F) for all premisses
    findall(premiss_node(F), member(F, AllPremisses), PremissTrees),
    % Get the conclusion formula
    fitch_line(RootLineNum, FinalFormula, _, _),
    
    % Create the forced node
    FinalTree = n_ary_premiss_node(FinalFormula, PremissTrees).

% =========================================================================
% BUSSPROOFS TREE CONSTRUCTION
% =========================================================================

build_buss_tree(LineNum, FitchLines, Tree) :-
    ( member(LineNum-Formula-Just-Scope, FitchLines) ->
        % Check if there's a more recent assumption with the same formula in a deeper scope
        ( member(HypNum-Formula-assumption-HypScope, FitchLines),
          HypNum > LineNum,
          HypScope > Scope ->
            % Use the hypothesis directly instead of reconstructing from LineNum
            Tree = assumption_node(Formula, HypNum)
        ;
            % Normal case: build tree from justification
            build_tree_from_just(Just, LineNum, Formula, FitchLines, Tree)
        )
    ;
        fail
    ).

% -- Reiteration (Rule moved for priority, fixes P, Q |- P) --
build_tree_from_just(reiteration(SourceLine), _LineNum, Formula, FitchLines, reiteration_node(Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% -- Leaves --
build_tree_from_just(assumption, LineNum, Formula, _FitchLines, assumption_node(Formula, LineNum)) :- !.
% Axiom in G4 (A |- A) must be rendered as R (reiteration) in tree-style ND
build_tree_from_just(axiom, _LineNum, Formula, _FitchLines, reiteration_node(Formula, axiom_node(Formula))) :- !.
build_tree_from_just(premiss, _LineNum, Formula, _FitchLines, premiss_node(Formula)) :- !.

% -- Implication Rules --
% R->
build_tree_from_just(rcond(HypNum, GoalNum), _LineNum, Formula, FitchLines, discharged_node(rcond, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(GoalNum, FitchLines, SubTree).

% L0-> (Modus Ponens)
build_tree_from_just(l0cond(MajLine, MinLine), _LineNum, Formula, FitchLines, binary_node(l0cond, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(MajLine, FitchLines, TreeA), build_buss_tree(MinLine, FitchLines, TreeB).

% L->-> (Special G4 Rule)
build_tree_from_just(ltoto(Line), _LineNum, Formula, FitchLines, unary_node(ltoto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Disjunction Rules --
% R∨ (Intro Or)
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L∨ (Elim Or) - Ternary
build_tree_from_just(lor(DisjLine, HypA, HypB, GoalA, GoalB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !, build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(GoalA, FitchLines, TreeA),
    build_buss_tree(GoalB, FitchLines, TreeB).

% L∨-> (Left disjunction to conditional)
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Conjunction Rules --
% L∧ (Elim And)
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R∧ (Intro And)
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% L∧-> (Left conjunction to conditional)
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Falsum / Negation Rules --
% L⊥ (Bot Elim)
build_tree_from_just(lbot(BotLine), _LineNum, Formula, FitchLines, unary_node(lbot, Formula, SubTree)) :-
    !, build_buss_tree(BotLine, FitchLines, SubTree).

% IP (Indirect proof / Classical)
build_tree_from_just(ip(HypNum, BotNum), _LineNum, Formula, FitchLines, discharged_node(ip, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(BotNum, FitchLines, SubTree).

% -- Quantifier Rules --
% L∃ (Exist Elim)
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines, 
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree), build_buss_tree(GoalNum, FitchLines, GoalTree).

% R∃ (Exist Intro)
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% L∀ (Forall Elim)
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% R∀ (Forall Intro)
build_tree_from_just(rall(BodyLine), _LineNum, Formula, FitchLines, unary_node(rall, Formula, SubTree)) :-
    !, build_buss_tree(BodyLine, FitchLines, SubTree).

% Quantifier Conversions
build_tree_from_just(cq_c(Line), _LineNum, Formula, FitchLines, unary_node(cq_c, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

build_tree_from_just(cq_m(Line), _LineNum, Formula, FitchLines, unary_node(cq_m, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Equality Rules --
build_tree_from_just(eq_refl, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.

build_tree_from_just(eq_sym(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_sym, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_trans(Line1, Line2), _LineNum, Formula, FitchLines, 
                     binary_node(eq_trans, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_subst(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_cong(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_cong, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_subst_eq(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst_eq, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_trans_chain, _LineNum, Formula, _FitchLines, 
                     axiom_node(Formula)) :- !.

% Fallback
build_tree_from_just(Just, LineNum, Formula, _FitchLines, unknown_node(Just, LineNum, Formula)) :-
    format('% WARNING: Unknown justification type: ~w~n', [Just]).

% =========================================================================
% RECURSIVE TREE RENDERING (LaTeX Bussproofs)
% =========================================================================

% render_buss_tree(+Tree)
% Generates LaTeX commands for the tree

% -- Leaves --
render_buss_tree(axiom_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

render_buss_tree(premiss_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Assumptions (FIXED STYLE: Number in small size, noLine, Formula) --
render_buss_tree(assumption_node(F, HypNum)) :-
    format('\\AxiomC{\\scriptsize{~w}}', [HypNum]), nl,
    write('\\noLine'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Reiteration --
render_buss_tree(reiteration_node(F, SubTree)) :-
    render_buss_tree(SubTree),
    % Fix: Use write/nl to ensure inference is rendered
    write('\\RightLabel{\\scriptsize{R}}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- N-ary FORCED nodes for displaying all premisses (simple conclusion case) --
render_buss_tree(n_ary_premiss_node(F, Trees)) :-
    % 1. Render all subtrees (premisses)
    maplist(render_buss_tree, Trees),
    
    % 2. Add Wk (Weakening) label
    write('\\RightLabel{\\scriptsize{Wk}}'), nl,
    
    % 3. Use BinaryInfC if N=2 (P and Q)
    length(Trees, N),
    ( N = 2 ->
        % BinaryInfC command takes the last two AxiomC, exactly matching the P, Q |- P requirement
        write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
    ;
        % For N > 2, use TrinaryInfC if possible, otherwise a message
        ( N = 3 ->
            write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        ;
            % If N>3 (unlikely for simple proof), fall back to BinaryInfC to keep document compilable
            format('% Warning: Simplified N=~w inference to BinaryInfC for display.~n', [N]),
            write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        )
    ).

% -- Unary Nodes --
render_buss_tree(unary_node(Rule, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Binary Nodes --
render_buss_tree(binary_node(Rule, F, TreeA, TreeB)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Ternary Nodes --
render_buss_tree(ternary_node(Rule, HypA, HypB, F, TreeA, TreeB, TreeC)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    render_buss_tree(TreeC),
    format_rule_label(Rule, Label),
    ( Rule = lor -> 
        format('\\RightLabel{\\scriptsize{~w} ~w,~w}~n', [Label, HypA, HypB])
    ; 
        format('\\RightLabel{\\scriptsize{~w}}~n', [Label])
    ),
    write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Nodes with Discharge (Assumptions) --
% For rcond (→I): check for vacuous discharge
render_buss_tree(discharged_node(rcond, HypNum, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(rcond, BaseLabel),
    % Check if discharge is vacuous (hypothesis doesn't appear in subtree)
    ( tree_contains_assumption(SubTree, HypNum) ->
        % Non-vacuous discharge: show hypothesis number
        format('\\RightLabel{\\scriptsize{~w}  ~w}~n', [BaseLabel, HypNum])
    ;
        % Vacuous discharge: don't show hypothesis number
        format('\\RightLabel{\\scriptsize{~w}}~n', [BaseLabel])
    ),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% For other rules (ip, rall): ALWAYS show hypothesis number (never vacuous)
render_buss_tree(discharged_node(Rule, HypNum, F, SubTree)) :-
    Rule \= rcond,  % Already handled above
    render_buss_tree(SubTree),
    format_rule_label(Rule, BaseLabel),
    % Always indicate the discharged assumption index
    format('\\RightLabel{\\scriptsize{~w}  ~w}~n', [BaseLabel, HypNum]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Special case for exists elimination
render_buss_tree(discharged_node(lex, WitNum, F, ExistTree, GoalTree)) :-
    render_buss_tree(ExistTree),
    render_buss_tree(GoalTree),
    format('\\RightLabel{\\scriptsize{$ \\exists E $ } ~w}~n', [WitNum]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Fallback
render_buss_tree(unknown_node(Just, _, F)) :-
    write('\\AxiomC{?'), write(Just), write('?}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% =========================================================================
% HELPER: RULE LABELS
% =========================================================================
format_rule_label(rcond, '$ \\to I $').
format_rule_label(l0cond, '$ \\to E $').
format_rule_label(ror, '$ \\lor I $').
format_rule_label(lor, '$ \\lor E $').
format_rule_label(land, '$ \\land E $').
format_rule_label(rand, '$ \\land I $').
format_rule_label(lbot, '$ \\bot E $').
format_rule_label(ip, ' IP ').
format_rule_label(lex, '$ \\exists E $').
format_rule_label(rex, '$ \\exists I $').
format_rule_label(lall, '$ \\forall E $').
format_rule_label(rall, '$ \\forall I $').
format_rule_label(ltoto, '$ \\to\\to E$').
format_rule_label(landto, '$ \\land\\to E$').
format_rule_label(lorto, '$ \\lor\\to E$').
format_rule_label(cq_c, ' $CQ_c $').
format_rule_label(cq_m, '$ CQ_m $').
format_rule_label(eq_refl, '$ = I $').
format_rule_label(eq_sym, ' Sym ').
format_rule_label(eq_trans, ' Trans ').
format_rule_label(eq_subst, '$ = E $').
format_rule_label(eq_cong, ' Cong ').
format_rule_label(eq_subst_eq, ' SubstEq ').
format_rule_label(X, X). % Fallback

% =========================================================================
% HELPER: WRAPPER FOR REWRITE
% =========================================================================
% Unified: always use write_formula_with_parens for consistent formatting
render_formula_for_buss(Formula) :-
    catch(
        (rewrite(Formula, 0, _, LatexFormula), write_formula_with_parens(LatexFormula)),
        _Error,
        (write('???'))
    ).


all_premisses_used(_, []) :- !.
all_premisses_used(Tree, [P|Ps]) :-
    tree_contains_formula(Tree, P),
    all_premisses_used(Tree, Ps).

% Helper: strip variable annotations
strip_annotations(![_-X]:Body, ![X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(?[_-X]:Body, ?[X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(A & B, SA & SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A | B, SA | SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A => B, SA => SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A <=> B, SA <=> SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(F, F).

% Match with annotation normalization
tree_contains_formula(premiss_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(axiom_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(hypothesis(_, F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(unary_node(_, _, SubTree), F) :- 
    tree_contains_formula(SubTree, F).
tree_contains_formula(binary_node(_, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).
tree_contains_formula(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F) ; tree_contains_formula(TreeC, F)).
tree_contains_formula(discharged_node(_, _, _, SubTree), F) :-
    tree_contains_formula(SubTree, F).
tree_contains_formula(discharged_node(_, _, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).

% =========================================================================
% VACUOUS DISCHARGE DETECTION
% =========================================================================
% tree_contains_assumption(+Tree, +HypNum)
% Succeeds if assumption with number HypNum appears in Tree

tree_contains_assumption(assumption_node(_, HypNum), HypNum) :- !.
tree_contains_assumption(assumption_node(_, _), _) :- !, fail.

tree_contains_assumption(reiteration_node(_, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(unary_node(_, _, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(binary_node(_, _, TreeA, TreeB), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ; tree_contains_assumption(TreeB, HypNum)).

tree_contains_assumption(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ; 
        tree_contains_assumption(TreeB, HypNum) ; 
        tree_contains_assumption(TreeC, HypNum)).

tree_contains_assumption(discharged_node(_, _, _, SubTree), HypNum) :-
    !, tree_contains_assumption(SubTree, HypNum).

tree_contains_assumption(discharged_node(_, _, _, TreeA, TreeB), HypNum) :-
    !, (tree_contains_assumption(TreeA, HypNum) ; tree_contains_assumption(TreeB, HypNum)).

tree_contains_assumption(n_ary_premiss_node(_, Trees), HypNum) :-
    !, member(Tree, Trees), tree_contains_assumption(Tree, HypNum).

% Leaves that can't contain assumptions
tree_contains_assumption(axiom_node(_), _) :- !, fail.
tree_contains_assumption(premiss_node(_), _) :- !, fail.
tree_contains_assumption(unknown_node(_, _, _), _) :- !, fail.

% =========================================================================
%   END OF ND TREE STYLE PRINTER 
% =========================================================================
%==========================================================================
% LATEX  UTILITIES
%========================================================================
%========================
% Fitch section
% ========================

% =========================================================================
% RENDERING PRIMITIVES
% =========================================================================

% render_hypo/7: Display a hypothesis in Fitch style

render_hypo(Scope, Formula, Label, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    write(' \\fh '),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Label),
    write('\\\\'), nl.


% render_fitch_indent/1: Genere l'indentation Fitch (\\fa)

render_fitch_indent(0) :- !.

render_fitch_indent(N) :- 
    N > 0,
    write('\\fa '),
    N1 is N - 1,
    render_fitch_indent(N1).

render_have(Scope, Formula, Just, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    % Always write \fa at level 0 (for sequents)
    ( Scope = 0 -> write('\\fa ') ; true ),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Just),
    write('\\\\'), nl.
 
% =========================================================================
% SIMPLE RULE: (Antecedent) => (Consequent) except for atoms
% =========================================================================

% Test if a formula is atomic
is_atomic_formula(Formula) :-
    atomic(Formula).

% -------------------------------------------------------------------------
% NEW: Test if a formula is a negation (in LaTeX display sense)
% A negative formula is represented as (' \\lnot ' X) par rewrite/4.
% We want to consider any formula starting with ' \\lnot ' as
% "non-parenthesable" - i.e. ne PAS entourer par des parentheses externe.
% -------------------------------------------------------------------------
is_negative_formula((' \\lnot ' _)) :- !.

% Helper: treat negative formulas as "atomic-like" for parentheses suppression
is_atomic_or_negative_formula(F) :-
    is_atomic_formula(F) ;
    is_negative_formula(F).

% =========================================================================
% TEST IF QUANTIFIER BODY NEEDS PARENTHESES
% =========================================================================

quantifier_body_needs_parens((_ ' \\to ' _)) :- !.
quantifier_body_needs_parens((_ ' \\land ' _)) :- !.
quantifier_body_needs_parens((_ ' \\lor ' _)) :- !.
quantifier_body_needs_parens((_ ' \\leftrightarrow ' _)) :- !.
quantifier_body_needs_parens(_) :- fail.

% =========================================================================
% ALL write_formula_with_parens/1 CLAUSES GROUPED
% =========================================================================

% Writing an implication with smart parentheses
write_formula_with_parens((A ' \\to ' B)) :-
    !,
    write_implication_with_parens(A, B).

write_formula_with_parens('='(A, B)) :- !,
    write('('), write_formula_with_parens(A), write(' = '), write_formula_with_parens(B), write(')').

% Autres operateurs
write_formula_with_parens((A ' \\lor ' B)) :-
    !,
    write_with_context(A, 'lor_left'),
    write(' \\lor '),
    write_with_context(B, 'lor_right').

write_formula_with_parens((A ' \\land ' B)) :-
    !,
    write_with_context(A, 'land_left'),
    write(' \\land '),
    write_with_context(B, 'land_right').

write_formula_with_parens((A ' \\leftrightarrow ' B)) :-
    !,
    write_bicond_component(A),
    write(' \\leftrightarrow '),
    write_bicond_component(B).

write_formula_with_parens((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    write_with_context(A, 'not').

% QUANTIFIERS WITH SMART PARENTHESES
write_formula_with_parens((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens(Other) :-
    write(Other).

% =========================================================================
% HELPER PREDICATES FOR BICONDITIONAL FORMATTING
% =========================================================================

% Helper: write biconditional component with parens if not a literal
write_bicond_component(A) :-
    is_latex_literal(A), !,
    write_formula_with_parens(A).
write_bicond_component(A ' \\to ' B) :- !,
    % Implications need parentheses in biconditional context
    write('('),
    write_implication_with_parens(A, B),
    write(')').
write_bicond_component(A) :-
    % Any other complex formula gets parentheses
    write('('),
    write_formula_with_parens(A),
    write(')').

% Check if a LaTeX formula is a literal (atom, negated atom, or predicate application)
is_latex_literal(A) :-
    atomic(A), !.
is_latex_literal((' \\lnot ' A)) :-
    atomic(A), !.
is_latex_literal((' \\lnot ' (' \\lnot ' A))) :-
    % Double negation of literal is still considered "atomic-like"
    is_latex_literal(A), !.
is_latex_literal(A) :-
    compound(A),
    A \= (_ ' \\to ' _),
    A \= (_ ' \\land ' _),
    A \= (_ ' \\lor ' _),
    A \= (_ ' \\leftrightarrow ' _),
    A \= (' \\lnot ' _),
    !.

% =========================================================================
% SPECIALIZED FUNCTION FOR IMPLICATIONS
% =========================================================================

write_implication_with_parens(Antecedent, Consequent) :-
    % Antecedent: do not parenthesize if atomic OR negative formula
    ( is_atomic_or_negative_formula(Antecedent) ->
        write_formula_with_parens(Antecedent)
    ;
        write('('),
        write_formula_with_parens(Antecedent),
        write(')')
    ),
    write(' \\to '),
    % Consequent: parenthesize except if atomic OR negative formula
    % NOTE: we consider any form (' \\lnot ' _) as "negative" even if
    % it contains several nested negations (~  ~ ~  A).
    ( is_atomic_or_negative_formula(Consequent) ->
        write_formula_with_parens(Consequent)
    ;
        write('('),
        write_formula_with_parens(Consequent),
        write(')')
    ).

% =========================================================================
% ALL write_with_context/2 CLAUSES GROUPED
% =========================================================================

% IMPLICATIONS in all contexts - use write_implication_with_parens
write_with_context((A ' \\to ' B), 'lor_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'lor_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'not') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

% CONJUNCTIONS in disjunctions
write_with_context((A ' \\land ' B), 'lor_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\land ' B), 'lor_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% CONJUNCTIONS in negations
write_with_context((A ' \\land ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% DISJUNCTIONS in negations
write_with_context((A ' \\lor ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% DISJUNCTIONS in conjunctions
write_with_context((A ' \\lor ' B), 'land_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\lor ' B), 'land_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% BICONDITIONALS in negations
write_with_context((A ' \\leftrightarrow ' B), 'not') :-
    !,
    write('('),
    write_bicond_component(A),
    write(' \\leftrightarrow '),
    write_bicond_component(B),
    write(')').

% FALLBACK CLAUSE
write_with_context(Formula, _Context) :-
    write_formula_with_parens(Formula).

% =========================================================================
% ADAPTED J.B. SYSTEM: direct rewrite on formulas with standard operators
% VERSION WITH ELEGANT PREDICATE SIMPLIFICATION
% =========================================================================

% rewrite/4 - Adapted version that handles formulas directly
rewrite(#, J, J, '\\bot') :- !.
rewrite(# => #, J, J, '\\top') :- !.

% NEW CLAUSE TO HANDLE SKOLEM CONSTANTS
% Converts f_sk(K,_) to a simple name like 'a', 'b', etc.
rewrite(f_sk(K,_), J, J, Name) :-
    !,
    rewrite_name(K, Name).

% BASE CASE: atomic formulas
rewrite(A, J, J, A_latex) :-
    atomic(A),
    !,
    toggle(A, A_latex).

% Recognizes ((A => B) & (B => A)) (or reverse order) as A <=> B for LaTeX display
% Must be placed BEFORE the generic rewrite((A & B), ...) clause
rewrite((X & Y), J, K, (C ' \\leftrightarrow ' D)) :-
    % cas 1 : X = (A => B), Y = (B => A)
    ( X = (A => B), Y = (B => A)
    % cas 2 : ordre inverse
    ; X = (B => A), Y = (A => B)
    ),
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Conjunction with standard operator &
rewrite((A & B), J, K, (C ' \\land ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Disjunction with standard operator |
rewrite((A | B), J, K, (C ' \\lor ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% AFFICHAGE COSMETIQUE : A => # devient !A
rewrite((A => #), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% Implication with standard operator =>
rewrite((A => B), J, K, (C ' \\to ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Biconditional with standard operator <=>
rewrite((A <=> B), J, K, (C ' \\leftrightarrow ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Negation with standard operator ~
rewrite((~A), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% QUANTIFICATEURS : Version Burse pour format X-Y
rewrite((![X-X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).

rewrite((?[X-X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).

rewrite((![X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur

rewrite((?[X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur
% =========================================================================
% SIMPLIFICATION ELEGANTE DES PREDICATS
% P(x,y,z) -> Pxyz for all predicates
% =========================================================================
% --- Replace the previous "concatenate predicate name and args" clause by this safer version.
% We avoid applying this cosmetic concatenation to equality and other logical operators.
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    % Do NOT collapse standard logical operators or equality into a single atom:
    % exclude '=' and the main logical connectives (=>, <=>, &, |, ~)
    \+ member(F, ['=', '=>', '<=>', '&', '|', '~']),
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).

% PREDICATES AND TERMS (general clause)
rewrite(X, J, K, Y) :-
    X =.. [F|L],
    toggle(F, G),
    rewrite_list(L, J, K, R),
    Y =.. [G|R].


% =========================================================================
% AUXILIARY PREDICATES FOR SIMPLIFICATION
% =========================================================================

all_simple_terms([]).
all_simple_terms([H|T]) :-
    simple_term(H),
    all_simple_terms(T).

simple_term(X) :-
    atomic(X), !.
simple_term(X) :-
    var(X), !.
simple_term(f_sk(_,_)) :-
    !.
simple_term(X) :-
    X =.. [F|Args],
    atom(F),
    Args \= [],
    length(Args, Len),
    Len =< 2,
    all_simple_terms(Args).

rewrite_args_list([], J, J, []).
rewrite_args_list([H|T], J, K, [RH|RT]) :-
    rewrite_term(H, J, TempJ, RH),
    rewrite_args_list(T, TempJ, K, RT).

concatenate_all([X], X) :-
    atomic(X), !.
concatenate_all([H|T], Result) :-
    length([H|T], Len),
    Len =< 5,
    !,
    concatenate_all_impl([H|T], Result).
concatenate_all(_, _) :-
    fail.

concatenate_all_impl([X], X) :-
    atomic(X), !.
concatenate_all_impl([H|T], Result) :-
    concatenate_all_impl(T, TempResult),
    atom_concat(H, TempResult, Result).

% =========================================================================
% LIST AND TERM PROCESSING
% =========================================================================

rewrite_list([], J, J, []).
rewrite_list([X|L], J, K, [Y|R]) :-
    rewrite_term(X, J, H, Y),
    rewrite_list(L, H, K, R).

rewrite_term(V, J, K, V) :-
    var(V),
    !,
    rewrite_name(J, V),
    K is J+1.

rewrite_term(f_sk(K,_), J, J, N) :-
    !,
    rewrite_name(K, N).

% NEW: If the term is a simple atom (constant), DO NOT capitalize it
% Because it is an argument of a predicate/function
rewrite_term(X, J, J, X) :-
    atomic(X),
    !.

rewrite_term(X, J, K, Y) :-
    X =.. [F|L],
    rewrite_list(L, J, K, R),
    Y =.. [F|R].

% Generateur de noms elegants
rewrite_name(K, N) :-
    K < 3,
    !,
    J is K+0'a,
    char_code(N, J).

rewrite_name(K, N) :-
    J is (K mod 3)+0'a,
    H is K div 3,
    number_codes(H, L),
    atom_codes(N, [J|L]).

% Toggle majuscules/minuscules
toggle(X, Y) :-
    atom_codes(X, L),
    toggle_list(L, R),
    atom_codes(Y, R).

toggle_list([], []).
toggle_list([X|L], [Y|R]) :-
    toggle_code(X, Y),
    toggle_list(L, R).

toggle_code(X, Y) :-
    0'a =< X, X =< 0'z,
    !,
    Y is X - 0'a + 0'A.

toggle_code(X, Y) :-
    0'A =< X, X =< 0'Z,
    !,
    Y is X - 0'A + 0'a.

toggle_code(X, X).

% =========================================================================
% SYSTEME PREPARE
% =========================================================================

prepare_sequent(PremissesList => Conclusion, PreparedPremisses, PreparedConclusion) :-
    is_list(PremissesList),
    !,
    prepare_premisses_list(PremissesList, PreparedPremisses),
    prepare(Conclusion, [], PreparedConclusion).

prepare_sequent(Premisses => Conclusion, [PreparedPremisses], PreparedConclusion) :-
    prepare(Premisses, [], PreparedPremisses),
    prepare(Conclusion, [], PreparedConclusion).

prepare_premisses_list([], []) :- !.
prepare_premisses_list([H|T], [PreparedH|PreparedT]) :-
    prepare(H, [], PreparedH),
    prepare_premisses_list(T, PreparedT).

prepare(#, _, #) :- !.

prepare((A & B), Q, (C & D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A | B), Q, (C | D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A => B), Q, (C => D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A <=> B), Q, (C <=> D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((~A), Q, (~C)) :-
    !,
    prepare(A, Q, C).

prepare((![Z]:A), Q, (![Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare((?[Z]:A), Q, (?[Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare(X, _, X) :-
    var(X),
    !.

prepare(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_term(X, _, X) :-
    var(X),
    !.

prepare_term(X, Q, Y) :-
    atom(X),
    member(X-Y, Q),
    !.

prepare_term(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_list([], _, []).
prepare_list([X|L], Q, [Y|R]) :-
    prepare_term(X, Q, Y),
    prepare_list(L, Q, R).

% Support lambda calculus
lambda_has(V:_, W) :-
    V == W.

lambda_has(app(P,_,_,_), W) :-
    lambda_has(P, W).

lambda_has(app(_,Q,_,_), W) :-
    lambda_has(Q, W).

lambda_has(lam(V:_,_,_,_), W) :-
    V == W,
    !,
    fail.

lambda_has(lam(_,P,_,_), W) :-
    lambda_has(P, W).

lambda_has('C'(P,_,_), W) :-
    lambda_has(P, W).

%%%%%% Sequents

% Determine proof type (theorem or sequent)
% RENAMED to avoid conflict with proof_type/2 from driver
% This function analyzes the STRUCTURE of a G4 proof, not the syntax of a formula
proof_structure_type(Proof, Type) :-
    proof_premisses(Proof, Premisses),
    (   Premisses = [] 
    ->  Type = theorem
    ;   Type = sequent
    ).

% NOTE: If proof_structure_type is used somewhere, update the calls.
% Currently, it does not seem to be called anywhere in this file.

% Generate Fitch commands according to type and position
fitch_prefix(sequent, LineNum, TotalPremisses, Prefix) :-
    (   LineNum =< TotalPremisses 
    ->  (   LineNum = TotalPremisses 
        ->  Prefix = '\\fj '  % Big flag for last premiss
        ;   Prefix = '\\fa '  % Normal line for premisses
        )
    ;   Prefix = '\\fa '      % Normal line after premisses
    ).

fitch_prefix(theorem, Depth, _, Prefix) :-
    (   Depth > 0 
    ->  Prefix = '\\fa \\fh '  % Small flag for hypotheses
    ;   Prefix = '\\fa '       % Ligne normale au niveau 0
    ).

% =========================================================================
% RENDU LATEX BUSSPROOFS
% =========================================================================

% =========================================================================
% LaTeX FORMULA RENDERING
% =========================================================================

% =========================================================================
% RENDER LATEX FORMULA - Unified with write_formula_with_parens
% =========================================================================
% Simply delegate to the unified formatting system

render_latex_formula(Formula) :-
    write_formula_with_parens(Formula).

render_latex_with_parens(Formula, Context) :-
    write_with_context(Formula, Context).

% =========================================================================
% END OF LATEX UTILITIES FILE
% =========================================================================
% =========================================================================
% LOGIC LEVEL DETECTION - Analyse holophrastique (Quine)
% Detection automatique : calcul propositionnel vs. calcul des predicats
% =========================================================================

:- dynamic formula_level/1.

% =========================================================================
% DETECTION PRINCIPALE
% =========================================================================

detect_and_set_logic_level(Formula) :-
    retractall(formula_level(_)),
    ( is_fol_formula(Formula) ->
        assertz(formula_level(fol))
    ;
        assertz(formula_level(propositional))
    ).

% =========================================================================
% HEURISTIQUES DE DETECTION FOL
% A formula is FOL if it contains:
% - Des quantificateurs (?, ?)
% - Predicate applications p(t1,...,tn) with n > 0
% - Equalities between terms
% - Des fonctions de Skolem
% =========================================================================

is_fol_formula(Formula) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)  
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.

% =========================================================================
% DETECTION DES COMPOSANTS
% =========================================================================

% Quantificateurs
contains_quantifier(![_-_]:_) :- !.
contains_quantifier(?[_-_]:_) :- !.
contains_quantifier(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_quantifier(Arg).


% Predicate applications (compound terms that are not connectives)
contains_predicate_application(Term) :-
    compound(Term),
    \+ is_logical_connective_structure(Term),
    Term =.. [_F|Args],
    Args \= [],  % Must have at least one argument
    !.
contains_predicate_application(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_predicate_application(Arg).

% Logical connective structures (to exclude)
is_logical_connective_structure(_ => _).
is_logical_connective_structure(_ & _).
is_logical_connective_structure(_ | _).
is_logical_connective_structure(_ <=> _).
is_logical_connective_structure(_ = _).  % Equality treated separately
is_logical_connective_structure(~ _).
is_logical_connective_structure(#).
is_logical_connective_structure(![_-_]:_).
is_logical_connective_structure(?[_-_]:_).

% Equality
contains_equality(_ = _) :- !.
contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_equality(Arg).

% Fonctions de Skolem
contains_function_symbol(f_sk(_,_)) :- !.
contains_function_symbol(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_function_symbol(Arg).

% =========================================================================
% FORMULA EXTRACTION FROM A G4 PROOF
% =========================================================================

extract_formula_from_proof(Proof, Formula) :-
    Proof =.. [_RuleName, Sequent|_],
    ( Sequent = (_ > [Formula]) -> 
        true
    ; Sequent = (_ > Goals), Goals = [Formula|_] -> 
        true
    ; 
        Formula = unknown
    ).
% =========================================================================
% VALIDATION & WARNINGS MODULE
% Detection of typing errors and misuse of logical operators
% =========================================================================
% This module validates formulas before proof attempt and warns about
% common mistakes, particularly the confusion between:
%   <=>  biconditional (propositional connective between formulas)
%   =    equality (relation between terms in FOL)
% =========================================================================


:- use_module(library(lists)).

% =========================================================================
% VALIDATION MODE CONFIGURATION
% =========================================================================
% Modes:
%   permissive - warn but continue (default)
%   strict     - reject invalid formulas automatically
%   silent     - no warnings

:- dynamic validation_mode/1.
validation_mode(permissive).

set_validation_mode(Mode) :-
    member(Mode, [permissive, strict, silent]),
    retractall(validation_mode(_)),
    assertz(validation_mode(Mode)).

% =========================================================================
% KNOWN PREDICATES REGISTRY
% =========================================================================
% Users can register predicate symbols to improve detection accuracy

:- dynamic known_predicate/1.

% Default predicates (common in logic examples)
known_predicate(p).
known_predicate(q).
known_predicate(r).
known_predicate(s).
known_predicate(h).
known_predicate(m).

register_predicate(P) :-
    \+ known_predicate(P),
    assertz(known_predicate(P)).

clear_predicates :-
    retractall(known_predicate(_)).

% =========================================================================
% MAIN VALIDATION ENTRY POINT
% =========================================================================

validate_and_warn(Formula, ValidatedFormula) :-
    validation_mode(Mode),
    
    % Check 1: Sequent syntax confusion (ALWAYS check, even in propositional logic)
    check_sequent_syntax_confusion(Formula, SyntaxWarnings),
    
    % Check 2: Biconditional misuse (only in FOL context)
    detect_fol_context(Formula, IsFOL),
    (   IsFOL ->
        check_bicond_misuse(Formula, BicondWarnings)
    ;   BicondWarnings = []
    ),
    
    % Combine warnings
    append(SyntaxWarnings, BicondWarnings, AllWarnings),
    
    % Handle combined warnings
    handle_warnings(AllWarnings, Mode, ValidatedFormula, Formula).

% Handle warnings according to mode
handle_warnings([], _, Formula, Formula) :- !.
handle_warnings(_Warnings, silent, Formula, Formula) :- !.
handle_warnings(Warnings, permissive, Formula, Formula) :-
    report_warnings(Warnings),
    prompt_continue.
handle_warnings(Warnings, strict, _, _) :-
    report_warnings(Warnings),
    write('? Validation failed in strict mode. Formula rejected.'), nl,
    fail.

% Prompt user to continue
prompt_continue :-
    write('Continue despite warnings? (y/n): '),
    read(Response),
    (   Response = y -> true
    ;   Response = yes -> true
    ;   write('? Proof attempt cancelled.'), nl, fail
    ).
% =========================================================================
% FOL CONTEXT DETECTION
% =========================================================================
% A formula is in FOL context if it contains:
%   - Quantifiers (?, ?)
%   - Predicate applications p(t1,...,tn) with n > 0
%   - Equality between terms
%   - Function symbols (including Skolem functions)

detect_fol_context(Formula, true) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.
detect_fol_context(_, false).

% Logical connective identification
is_logical_connective(_ => _).
is_logical_connective(_ & _).
is_logical_connective(_ | _).
is_logical_connective(_ <=> _).
is_logical_connective(~ _).
is_logical_connective(#).
is_logical_connective(![_-_]:_).
is_logical_connective(?[_-_]:_).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION
% =========================================================================
% Detects <=> used between terms instead of formulas
% Example: (a <=> b) should likely be (a = b) in FOL

check_bicond_misuse(Formula, Warnings) :-
    findall(Warning, detect_bicond_in_terms(Formula, Warning), Warnings).

% =========================================================================
% BICONDITIONAL MISUSE DETECTION (IMPROVED)
% =========================================================================
% Only warn if <=> appears in a TERM CONTEXT (not formula context)

detect_bicond_in_terms(A <=> B, warning(bicond_between_terms, A, B)) :-
    % Both sides are clearly terms (constants or function applications)
    is_definitely_term(A),
    is_definitely_term(B),
    !.

detect_bicond_in_terms(Term, Warning) :-
    compound(Term),
    Term \= (_ <=> _),  % Don't recurse into biconditionals we already checked
    Term =.. [_|Args],
    member(Arg, Args),
    detect_bicond_in_terms(Arg, Warning).

% =========================================================================
% DEFINITELY A TERM (not a formula)
% =========================================================================
% Conservative: only flag obvious cases

is_definitely_term(X) :- 
    var(X), !.  % Variable (term)

is_definitely_term(X) :- 
    atomic(X),
    \+ known_predicate(X),  % Constant, not predicate
    !.

is_definitely_term(f_sk(_,_)) :- !.  % Skolem function

is_definitely_term(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    % Must be a KNOWN function symbol (not predicate)
    is_known_function(F),
    !.

% =========================================================================
% KNOWN FUNCTION REGISTRY
% =========================================================================
% Users can register function symbols to improve detection

:- dynamic known_function/1.

% Default common function symbols
known_function(succ).   % Successor
known_function(plus).
known_function(times).
known_function(father).  % father(x) is a term
known_function(mother).

register_function(F) :-
    \+ known_function(F),
    assertz(known_function(F)).

is_known_function(F) :-
    known_function(F), !.

% Heuristic fallback: if NOT a known predicate, assume function
% (This is conservative - avoid false positives)
is_known_function(F) :-
    \+ known_predicate(F),
    \+ member(F, [f, g, h, i, j, k, p, q, r, s]),  % Ambiguous symbols
    !.

% =========================================================================
% SEQUENT SYNTAX CONFUSION DETECTION
% =========================================================================
% Detects common mistakes:
%   [P] => [Q]  (WRONG - looks like sequent but uses =>)
%   P > Q       (WRONG - looks like implication but uses >)

check_sequent_syntax_confusion(Formula, Warnings) :-
    findall(Warning, detect_sequent_confusion(Formula, Warning), Warnings).

% Case 1: [List] => [List] - user probably meant sequent syntax
detect_sequent_confusion([_|_] => [_|_], warning(list_implication, 'Use > for sequents, not =>')) :- !.
detect_sequent_confusion([_|_] => _, warning(list_implication_left, 'Left side is a list - use > for sequents')) :- !.
detect_sequent_confusion(_ => [_|_], warning(list_implication_right, 'Right side is a list - use > for sequents')) :- !.

% Case 2: Atom > Atom - user probably meant implication
detect_sequent_confusion(A > B, warning(atom_turnstile, 'Use => for implication, not >')) :-
    atomic(A),
    atomic(B),
    !.

% Case 3: Complex formula > Complex formula - likely implication
detect_sequent_confusion(A > B, warning(formula_turnstile, 'Use => for implication between formulas, not >')) :-
    is_formula(A),
    is_formula(B),
    !.

% Recursive search
detect_sequent_confusion(Term, Warning) :-
    compound(Term),
    Term \= (_ => _),  % Don't recurse into implications
    Term \= (_ > _),   % Don't recurse into turnstiles
    Term =.. [_|Args],
    member(Arg, Args),
    detect_sequent_confusion(Arg, Warning).

% Helper: check if something is a formula (not a list or term)
is_formula(Term) :-
    compound(Term),
    (   is_logical_connective(Term)
    ;   Term =.. [F|Args], Args \= [], known_predicate(F)
    ).

% Term identification (not a formula)
% A term is: constant, variable, or function application
is_term_not_formula(X) :- 
    atomic(X), !.  % Constant or variable
is_term_not_formula(f_sk(_,_)) :- !.  % Skolem function
is_term_not_formula(Term) :-
    compound(Term),
    \+ is_logical_connective(Term),
    Term =.. [F|Args],
    Args \= [],
    \+ known_predicate(F),  % Function, not predicate
    !.

% =========================================================================
% WARNING REPORTS
% =========================================================================

report_warnings([]) :- !.
report_warnings(Warnings) :-
    length(Warnings, N),
    nl,
    format('?  ~d WARNING(S) DETECTED:~n', [N]),
    nl,
    maplist(print_warning, Warnings),
    nl,
    write('? TIPS:'), nl,
    write('   o Theorems:  prove(p => q).        % implication'), nl,
    write('   o Sequents:  prove([p] > [q]).     % turnstile ?'), nl,
    write('   o FOL:       use = for equality, <=> for biconditional'), nl,
    nl.

print_warning(warning(bicond_between_terms, A, B)) :-
    format('   ?  (~w <=> ~w): biconditional between terms detected.~n', [A, B]),
    format('      -> Did you mean (~w = ~w)?~n', [A, B]).

% NEW: Sequent syntax warnings
print_warning(warning(list_implication, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove([p, q] > [p & q]).  % CORRECT'), nl,
    write('               prove([p, q] => [p & q]). % WRONG'), nl.

print_warning(warning(list_implication_left, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(list_implication_right, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use [Premisses] > [Conclusion] for sequents'), nl.

print_warning(warning(atom_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      Example: prove(p => q).       % CORRECT (implication)'), nl,
    write('               prove(p > q).        % WRONG'), nl,
    write('               prove([p] > [q]).    % CORRECT (sequent)'), nl.

print_warning(warning(formula_turnstile, Msg)) :-
    format('   ?  Syntax error: ~w~n', [Msg]),
    write('      -> Use => for implications, > only for sequents'), nl,
    write('      -> Sequent syntax: [Premisses] > [Conclusions]'), nl.

% =========================================================================
% UTILITY: AUTO-SUGGESTION (optional feature)
% =========================================================================
% Suggests automatic correction of <=> to = in term contexts

suggest_auto_correction(Formula, CorrectedFormula) :-
    replace_bicond_with_eq(Formula, CorrectedFormula).

replace_bicond_with_eq(A <=> B, A1 = B1) :-
    is_term_not_formula(A),
    is_term_not_formula(B),
    !,
    replace_bicond_with_eq(A, A1),
    replace_bicond_with_eq(B, B1).
replace_bicond_with_eq(Term, Result) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(replace_bicond_with_eq, Args, NewArgs),
    Result =.. [F|NewArgs], !.
replace_bicond_with_eq(Term, Term).

%%% END OF PROVER ONLINE
