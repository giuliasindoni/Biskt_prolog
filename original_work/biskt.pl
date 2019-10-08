
%% TO DO LIST
%% Add a predicate "add_if_new" to add new formulae to
%% a branch. This would only add formulae that are not
%% already present in the branch.


%% This just to write the status
refute( Formulae, _ ) :-
        write( 'refute: ' ), write(Formulae), nl,
        %write( '        ' ), write(Rules), nl,
        fail. 

%% CLOSING RULES -------------------------------

refute( Formulae, [tf_close] ) :-
   select( S:(Phi=t), Formulae, Rest ),
   member( S:(Phi=f),  Rest ), !,
   applying( tf_close ).

refute( Formulae, [false_is_t_close] ) :-
      member( _:(false=t), Formulae ), !,
      applying( false_is_t_close ).


%% NON-BRANCHING RULES

%% True conjunction
%% Remove true conjunctive formula and replace by its separate 
%% conjuncts (at same world)
refute( Formulae, [t_con | Rules] ) :-
        select( S:(and(Phi,Psi)=t), Formulae, Rest ),
        ( \+(member(S:(Phi = t), Rest))
        	;
          \+(member(S: (Psi =t), Rest))
        ),
        !,
        applying( t_con ),
        refute( [S:(Phi=t), S:(Psi=t) | Rest], Rules ).

%% False disjunction
%% Remove false disjunctive formula and replace by its 
%% separate false disjuncts (at same world)
refute( Formulae, [f_dis | Rules] ) :-
        select( S:(or(Phi,Psi)=f), Formulae, Rest ),
        (\+(member(S:(Phi = f), Rest))
          ;
          \+(member(S: (Psi =f), Rest))
        ),
        !,
        applying(f_dis),
        refute( [S:(Phi=f), S:(Psi=f) | Rest], Rules ).


%% True node first negation
%% Note: In this rule we are unpacking a true nneg formula
%% with respect to an h-succssor world.
%% We remove the negation and add that the remaining formula
%% is false at the h-successor world.
%% No formula is removed.
%% But the rule will be blocked if the consequence is already
%% present in the formula set being refuted.
%% 
refute( Formulae, [t_nneg | Rules] ) :-
        select( S:(nneg(Phi)=t), Formulae, Rest ),
        member( h(S,T), Rest ), 
        \+( member( T:(Phi=f), Rest ) ),
        !,
        applying(t_nneg),
        refute( [T:(Phi=f) | Formulae], Rules ).

% %% True node first negation --- special case with T=S
 refute( Formulae, [t_nneg_s | Rules] ) :-
         select( S:(nneg(Phi)=t), Formulae, Rest ),
         \+( member( S:(Phi=f), Rest ) ),
         !,
         applying(t_nneg_s),
         refute( [S:(Phi=f) | Rest], Rules ).


%% False edge first negation
%% This is symmetric with t_nneg
refute( Formulae, [f_eneg | Rules] ) :-
        select( S:(eneg(Phi)=f), Formulae, Rest ),
        member( h(T,S), Rest ),
        \+( member( T:(Phi=t), Rest ) ),
        !,
        applying(f_eneg),
        refute( [T:(Phi=t) | Formulae], Rules ).

%% False edge first negation --- special case with T=S
refute( Formulae, [f_eneg_s | Rules] ) :-
        select( S:(eneg(Phi)=f), Formulae, Rest ),
        \+( member( S:(Phi=t), Rest ) ),
        !,
        applying(f_eneg_s),
        refute( [S:(Phi=t) | Formulae], Rules ).


%% True white box 
refute(Formulae, [t_whitebox | Rules]) :-
       select( S: (whitebox(Phi) = t), Formulae, Rest),
       member(r(S, T), Rest),
       \+(member( T: (Phi = t), Rest)), !, %% Check not already present
       applying(t_whitebox ),
       refute([T: (Phi = t) | Formulae ], Rules). 


%% False black diamond
refute(Formulae, [f_blackdia | Rules]) :-
      select(S: ( blackdia(Phi) = f), Formulae, Rest),
      member(r(T, S), Rest),
      \+(member(T: (Phi = f), Rest)), !, %% Check not already present
      applying(f_blackdia),
      refute([T: (Phi = f) | Formulae], Rules).

%% True everywhere

refute(Formulae, [t_ubox| Rules]) :-
      select( _S: (ubox(Phi) = t),  Formulae, Rest),
      member( T: (_), Formulae), %% Here we look for the formulae in Formulae and not in Rest because the world S with the ubox has to be considered as well
      \+(member( T: (Phi = t), Rest)), %% Check not already present
      !,
      applying(t_ubox),
      refute([T: (Phi = t) | Formulae], Rules).

%%False somewhere

refute(Formulae, [f_udia| Rules]) :-
       select( _S: (udia(Phi) = f), Formulae, Rest),
         member( T: ( _ ), Formulae),
         \+(member( T: (Phi = f), Rest)),
         !,
         applying(f_udia),
         refute([T: (Phi = f) | Formulae], Rules). 


%% Frame rule for h relation

%% Monotonicity of truth wrt h
refute( Formulae, [h_mon | Rules] ) :-
      member( S:(Phi=t), Formulae ),
      member( h(S,T), Formulae ),
      \+( member(T:(Phi=t), Formulae) ), %% Check not already present
      !,
      applying( h_mon ),
      refute( [ T:(Phi=t) | Formulae ], Rules ).

%% Transitivity of h
refute( Formulae, [h_trans | Rules] ) :-
      member( h(S,T), Formulae ),
      member( h(T,U), Formulae ),
      \+( member( h(S,U), Formulae) ), %% Check not already present
      !,
      applying( h_trans ), 
      refute( [h(S,U) | Formulae], Rules ).


%% Frame rules for r relation

%% r is stable

refute(Formulae, [r_stable | Rules]) :-
      member(h(S, T), Formulae),
      member(r(T, Z), Formulae),
      member(h(Z, Y), Formulae),
      \+(member(r(S, Y), Formulae)), %% Check not already present
      !,
      applying(r_stable),
      refute([r(S, Y) | Formulae], Rules).



%% BRANCHING RULES ----------------------------

%% True disjunction
refute( Formulae, [t_dis, [t_dis_B1 | Rules1], [d_dis_B2 | Rules2] ] ) :-
        select( S:(or(Phi,Psi)=t), Formulae, Rest ), 
         \+(member(S:(Phi = t), Rest)),
        \+(member(S: (Psi =t), Rest)),
        !,
        applying(t_dis),
        refute( [S:(Phi=t) | Rest], Rules1 ), 
        refute( [S:(Psi=t) | Rest], Rules2 ).


%% False conjunction
refute( Formulae, [f_con, [f_con_B1 | Rules1], [f_com_B2 | Rules2] ] ) :-
        select( S:(and(Phi,Psi)=f), Formulae, Rest ),
        \+(member(S:(Phi = f), Rest)),
        \+(member(S: (Psi =f), Rest)),
        !,
        applying(f_con),
        refute( [S:(Phi=f) | Rest], Rules1 ), 
        refute( [S:(Psi=f) | Rest], Rules2 ).

%% True implications
%% We keep the implication in case it needs to be used again.
%% But the rule is blocked if either of the alternative new formulae
%% is already present in the branch.
refute( Formulae, [t_imp, [t_imp_B1 | Rules1], [t_imp_B2 | Rules2] ]  ) :-
        select( W:(imp(Phi,Psi)=t), Formulae, Rest ),
        member( h(W,W2), Rest ),
        \+(member( W2:(Phi=f), Rest ) ),
        \+(member( W2:(Psi=t), Rest ) ), 
        !,
        applying(t_imp),
        refute( ['B1', W2:(Phi=f) | Formulae], Rules1 ), 
        refute( ['B2', W2:(Psi=t) | Formulae], Rules2 ). 

/*

 %% WORLDS-CONTRACTION RULE (BLOCKING)



refute(Formulae, [contr_rule | Rules]) :-
       delete_label_prime(_S, _T, Formulae, Contr_formulae),
       refute(Contr_formulae, Rules).
*/

%% CREATING RULES ORIGINAL NON-BRANCHING VERSION ------------------------------------

%% False node first negation
refute( Formulae, [f_nneg | Rules] ) :-
        select( S:(nneg(Phi)=f), Formulae, Rest ),
        ( \+(member(h(S, X), Rest))  ;
          \+( member(X:(Phi =t), Rest))),
        !,
        applying( f_nneg ),
        T = @(nneg(Phi),S),
        refute( [h(S,T), h(T,T), T:(Phi=t) | Rest], Rules ). 

%% True edge first negation
refute( Formulae, [t_eneg | Rules] ) :-
        select( S:(eneg(Phi)=t), Formulae, Rest ),
         ( \+(member(h(X, S), Rest))  ;
          \+( member(X:(Phi =f), Rest))),
        !,
        applying( t_eneg ),
        T = @(eneg(Phi),S),
        refute( [h(T,S), h(T,T), T:(Phi=f) | Rest], Rules ). 

%% False implication
 refute( Formulae, [f_imp | Rules] ) :-
        select( W:(imp(Phi,Psi)=f), Formulae, Rest ),
        ( \+(member(h(W, X), Rest))  ;
          \+( member(X:(Phi =t), Rest)) ;
          \+(member(X:(Psi= f), Rest))),
        !,
        applying( f_imp ),
        W1 = @(imp(Phi,Psi),W),
        refute( [h(W,W1), h(W1,W1), W1:(Phi=t), W1:(Psi=f) | Rest], Rules ). 



%% False white box


refute(Formulae, [f_whitebox | Rules]) :-
        select(S: (whitebox(Phi) = f), Formulae, Rest),
        ( \+(member(r(S, X), Rest))  ;
        \+( member(X:(Phi = f), Rest))),
        !,
        applying(f_whitebox),
        T =  @(whitebox(Phi),S),
        refute([r(S, T), h(T,T), T: (Phi = f) | Rest], Rules). 


/*

%% False white box, branching version

refute(Formulae, [f_whitebox, [f_whitebox_B1 | Rules1], [f_whitebox_B2 | Rules2]]) :-
        select(S: (whitebox(Phi) = f), Formulae, Rest),
        ( \+(member(r(S, X), Rest))  ;
        \+( member(X:(Phi = f), Rest))),
        !,
        applying(f_whitebox),
        T =  @(whitebox(Phi),S),
        refute([r(S, S), S:(Phi = f) | Rest ], Rules1),
        refute([r(S, T), h(T,T), T: (Phi = f) | Rest], Rules2). 


%% False white box, second branching version

refute(Formulae, [f_whitebox, [f_whitebox_B1 | Rules1], [f_whitebox_B2 | Rules2]]) :-
      select(S: (whitebox(Phi) = f), Formulae, Rest),
      member(Y:(_), Formulae),
      ( \+(member(r(S, X), Rest))  ;
        \+( member(X:(Phi =f), Rest))),
      !,
      applying(f_whitebox),
      T = @(whitebox(Phi),S),
      refute([r(S, Y), Y:(Phi = f) | Rest], Rules1),
      refute([r(S, T), h(T,T), T: (Phi = f) | Rest], Rules2).

*/



%% True black dia

refute(Formulae, [t_blackdia | Rules]) :-
      select(S: (blackdia(Phi) = t), Formulae, Rest),
      ( \+(member(r(X, S), Rest))  ;
        \+( member(X:(Phi =t), Rest))),
      !,
      applying(t_blackdia),
      T = @(blackdia(Phi),S),
      refute([r(T, S), h(T,T), T: (Phi = t) | Rest], Rules).
/*

%% True black dia, branching version

refute(Formulae, [t_blackdia, [t_blackdia_B1 | Rules1], [t_blackdia_B2 | Rules2]]) :-
      select(S: (blackdia(Phi) = t), Formulae, Rest),
      ( \+(member(r(X, S), Rest))  ;
        \+( member(X:(Phi =t), Rest))),
      !,
      applying(t_blackdia),
      T = @(blackdia(Phi),S),
      refute([r(S, S), S:(Phi = t) | Rest], Rules1),
      refute([r(T, S), h(T,T), T: (Phi = t) | Rest], Rules2).




%% True black dia, second branching version

refute(Formulae, [t_blackdia, [t_blackdia_B1 | Rules1], [t_blackdia_B2 | Rules2]]) :-
      select(S: (blackdia(Phi) = t), Formulae, Rest),
      member(Y:(_), Formulae),
      ( \+(member(r(X, S), Rest))  ;
        \+( member(X:(Phi =t), Rest))),
      !,
      applying(t_blackdia),
      T = @(blackdia(Phi),S),
      refute([r(Y, S), Y:(Phi = t) | Rest], Rules1),
      refute([r(T, S), h(T,T), T: (Phi = t) | Rest], Rules2).

*/

%% False universal box

refute(Formulae, [f_ubox | Rules]) :-
       select(S: (ubox(Phi) = f), Formulae, Rest),
       \+(member(_X:(Phi = f), Rest)),
       !,
       applying(f_ubox),
       T = @(ubox(Phi),S),
       refute([T: (Phi = f), h(T,T) | Rest], Rules).



%% True universal diamond 

refute(Formulae, [t_udia | Rules]) :- 
      select(S:(udia(Phi) = t), Formulae, Rest),
      \+(member(_X:(Phi = t), Rest)),
       !,
       applying(t_udia),
       T = @(udia(Phi), S),
      refute([T: (Phi = t), h(T, T) | Rest], Rules).



%% -------------------------------------
refute( Formulae, _ ) :- !,
      write( '!! CANNOT REFUTE !!' ), nl,
      write( '!! No rule applicable to the current formula set:'), nl,
      showlist_ind( Formulae), nl, nl,
      fail.
%%---------------------------------

first_to_last( [],[]).

first_to_last( [H|T], L) :- append(T,[H], L).

add_labels_h_reflexivity( [], [] ).

add_labels_h_reflexivity( [S:F | Rest], [S:F, h(S,S) | AddRefRest] ) :- 
         \+( member( h(S,S), Rest ) ), !,
         add_labels_h_reflexivity( Rest, AddRefRest ). 

add_labels_h_reflexivity( [S:F | Rest], [S:F | AddRefRest] ) :- 
         !,
         add_labels_h_reflexivity( Rest, AddRefRest ). 


different_formulae(Lab1, Lab2, List) :- 
                                      member(Lab1:(F1= S1), List),
                                      \+(member(Lab2:(F1 = S1), List)).

lab1_in_lab2(Lab1, Lab2, List) :- \+(different_formulae(Lab1, Lab2, List)), \+(Lab1 = Lab2).


subset_with_label( Sub, Label, Set ) :- setof( X, 
                                            P^(member(X, Set), X= Label:P ), 
                                            Sub  
                                           ).


delete_label_prime(Lab1, Lab2, InitialList, FinalList) :- lab1_in_lab2(Lab2, Lab1, InitialList),
                                                          subset_with_label(ListLab2, Lab2, InitialList),
                                                          subtract(InitialList, ListLab2, FinalList).





showlist_ind([]).
showlist_ind([H|T]) :- write('     '), write(H), nl, showlist_ind(T).


applying( Rule ):- write('Applying: '), write(Rule), nl.

example(0, 
        [i:(and(eneg(nneg(p1)), p2 ) = t), h(j,i), h(j,v) ],
        v:(and(p1, eneg(nneg(p2))) = t)
        ).

example(01,
          [i: (and(eneg(nneg(p1)) ,p2) = t), v: ( and(p1, eneg(nneg(p2))) = f) , h(t,i), h(t,v) ],
          inconsistent).



example(1, [],
           i: (imp(p, eneg(nneg(p)) ) = t) ).


example( 2,
         [i:(p2=t)],
          i:(imp(p1,p2)=t)
       ). 

example( 3,
         [ i:(nneg(p1)=t), i:(p1=t)],
           inconsistent 
       ).


example(4, [i: (imp(or(p, nneg(nneg(p))),nneg(nneg(p))) =f)],
           inconsistent
        ).


example(5, [], 
  i: (imp(or(p, nneg(nneg(p))),nneg(nneg(p))) =t)).



example(6, [i: (imp( (nneg(eneg(p))), (eneg(eneg(p)))) = f) ], 
             inconsistent).


example(7, [], i: (imp( nneg(eneg(p)), eneg(eneg(p)))  = t) ).

example(8, [], 
           i: (imp(blackdia(whitebox(p)) ,p) = t)).


example(9, [],
             i: (imp(p, whitebox(blackdia(p))) = t) ).


example(10, [],
             i: (imp((blackdia(or(p1, p2))) , (or(blackdia(p1) ,blackdia(p2) ) )) = t)  ).

example(11, [],
            i:(imp((or(blackdia(p1) ,blackdia(p2))), (blackdia(or(p1, p2)))) = t )).

%% Example12: not sure this actually works: the last rule applied is true conj for some odd reason
%% it should be tf_close

example(12, [], i: (imp(udia(and( eneg(nneg(p1)) , p2) ), udia(and(p1, eneg(nneg(p2))) ) )  = t)).


%%Example 13: try to refute that the formula is false, but it cannot refute%% as model exists

example(13, [], 
	    i:(ubox(udia(p1)) = t)).

example(14, [], 
	    i:(ubox(udia(p1)) = f) ).

example(15, [], 
  i: (ubox(and(p1, p2)) = f) ).


example(16, [], 
  i: (udia(nneg(p1)) = t )).


example(17, [],
         i: (nneg(p1)=f)).


example(18, [],
         i: (eneg(p1)=t)).

example(19, [],
        i: (udia(or(p1, p2)) =t)).

example(20, [],
        i: (ubox(or(p1, p2)) =f)).


example(21, [], 
  i: (ubox(eneg(p1)) = f )).


example(22, [], 
  i: (ubox(blackdia(p1)) = f )).

example(23, [], 
  i: (udia(imp(and(p1,p2), p2)) = t )).

example(24, [], 
      i:(udia(ubox(p1)) = t) ).



example(25, [], 
  i: (udia(whitebox(p1)) = t )).




example(26, [], 
  i: (udia(imp(p1, p2)) = t )).
        
example(27, [], 
  i: (udia(whitebox(p1)) = t )).


prove( EgN, Rules ) :-
       example( EgN, Premisses, Conclusion ),
       write(proving(EgN)),
       ( Conclusion = inconsistent 
         ->
         FormulaSet = Premisses
         ;
         ( Conclusion = S:(Phi=TorF),
           member( TorF=ForT, [ t=f, f=t] ),
           FormulaSet = [ S:(Phi=ForT) | Premisses ]
         )
       ),
       add_labels_h_reflexivity( FormulaSet, FormulaSet_withReflexH ),
       refute( FormulaSet_withReflexH, Rules ).


run(N) :- prove( N, Rules ), !,
          format( "** Proved example ~p (refutation tableau closed).~n", [N]),
          format( "Rule sequence is: ~p", [Rules] ).

run(N) :- format( "!! Could not prove example ~p", [N]).


run :- run(12).

:-  initialization(run). 


















