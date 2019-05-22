

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
        select( S:(and(Phi,Psi)=t), Formulae, Rest ), !,
        applying( t_con ),
        refute( [S:(Phi=t), S:(Psi=t) | Rest], Rules ).

%% False disjunction
%% Remove false disjunctive formula and replace by its 
%% separate false disjuncts (at same world)
refute( Formulae, [f_dis | Rules] ) :-
        select( S:(or(Phi,Psi)=f), Formulae, Rest ), !,
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

%% True node first negation --- special case with T=S
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
 refute( Formulae, [t_wbox | Rules]) :-
 select( W:(wbox(Phi) = t), Formulae, Rest ),
 member(r(W, W2), Rest),
 \+( member(W2: (Phi=t), Rest) ),
 !,
 applying(t_wbox),
 refute([W2:(Phi=t) | Formulae], Rules ). 




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


%% BRANCHING RULES ----------------------------

%% True disjunction
refute( Formulae, [t_dis, [t_dis_B1 | Rules1], [d_dis_B2 | Rules2] ] ) :-
        select( S:(or(Phi,Psi)=t), Formulae, Rest ), 
        !,
        applying(t_dis),
        refute( [S:(Phi=t) | Rest], Rules1 ), 
        refute( [S:(Psi=t) | Rest], Rules2 ).


%% False conjunction
refute( Formulae, [f_con, [f_con_B1 | Rules1], [f_com_B2 | Rules2] ] ) :-
        select( S:(and(Phi,Psi)=f), Formulae, Rest ),
        !,
        applying(f_con),
        refute( [S:(Phi=f) | Rest], Rules1 ), 
        refute( [S:(Psi=f) | Rest], Rules2 ).

%% True implications
%% This one not finished
%% We want to keep the implication (in both branches??)
%% NOT FINISHED YET !!!
refute( Formulae, [t_imp, [t_imp_B1 | Rules1], [f_imp__B2 | Rules2] ] ) :-
        select( W:(imp(Phi,Psi)=t), Formulae, Rest ),
        member( h(W,W2), Rest ),
        !,
        applying(t_imp),
        refute( ['B1', W2:(Phi=f) | Rest], Rules1 ), 
        refute( ['B2', W2:(Psi=t) | Rest], Rules2 ).


%% CREATING RULES ------------------------------------

%% False node first negation
refute( Formulae, [f_nneg | Rules] ) :-
        select( S:(nneg(Phi)=f), Formulae, Rest ),
        !,
        applying( f_nneg ),
        T = @(nneg(Phi),S),
        refute( [h(S,T), T:(Phi=t) | Rest], Rules ). 

%% True edge first negation
refute( Formulae, [t_eneg | Rules] ) :-
        select( S:(eneg(Phi)=t), Formulae, Rest ),
        !,
        applying( t_eneg ),
        T = @(eneg(Phi),S),
        refute( [h(T,S), T:(Phi=f) | Rest], Rules ). 

%% False implication
refute( Formulae, [f_imp | Rules] ) :-
        select( W:(imp(Phi,Psi)=f), Formulae, Rest ),
        !,
        applying( f_imp ),
        W1 = @(imp(Phi,Psi),W),
        refute( [h(W,W1), W1:(Phi=t), W1:(Psi=f) | Rest], Rules ). 






%% -------------------------------------
refute( Formulae, _ ) :- !,
      write( '!! CANNOT REFUTE !!' ), nl,
      write( '!! No rule applicable to the current formula set:'), nl,
      showlist_ind( Formulae), nl, nl,
      fail.
%%---------------------------------


showlist_ind([]).
showlist_ind([H|T]) :- write('     '), write(H), nl, showlist_ind(T).


applying( Rule ):- write('Applying: '), write(Rule), nl.



example( 1,
         [s: ( and( eneg(nneg(x)), y ) =t ), h(w,s), h(w,m)],  
          m:( and( x, eneg(nneg(y)) ) =t )
       ).

example( 2,
         [w:(q=t)],
          w:(imp(p,q)=t)
       ). 


prove( EgN, Rules ) :-
       example( EgN, Premisses, Conclusion ),
       Conclusion = S:(Phi=TorF),
       member( TorF=ForT, [ t=f, f=t] ),
       refute( [ S:(Phi=ForT) | Premisses ], Rules ).


run(N) :- prove( N, Rules ), !,
          format( "** Proved example ~p (refutation tableau closed).~n", [N]),
          format( "Rule sequence is: ~p", [Rules] ).

run(N) :- format( "!! Could not prove example ~p", [N]).

%[examples].

run :- run(1).

:- initialization(run).






















