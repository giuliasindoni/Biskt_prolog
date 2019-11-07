%% TO DO LIST:
%% we need a refute predicate such that 
%% if there no more rules applicable 
%% to a set of formulae (so an open branch)
%% then the refutation process fail 
%% and the formula set is shown
%% so that for example in the branching rules we do not refute both branches if the first one is open



%%We need to put a refute rule so that when no more rules
%%are applicable to a branch, so there is open branch,
%%the program fails and print this open branch with the message that the original formula cannot be refuted.
 

%% META-LEVEl RULES 

%% Objects are property value lists:
% e.g [prop1 = this, prop2 = [some, items]] ) 
% or
% [available = [.., ..], used = [...., ... ], relations = ???]

ob_prop_val( Object, Prop, Val ) :-
     member( Prop = Val, Object ).

%% The following rule lets us go from an old object to a new object

set_ob_prop_val( Object, Prop, Val, NewObject ) :-
     select( Prop = _, Object, Rest ),
     NewObject = [Prop=Val | Rest].

%% IN-BETWEEN RULES

%% The following rule specifies when a logic formula is in available-list

has_available_formula( State, Formula ) :-
          ob_prop_val( State, available, Formulae ),
          member( Formula, Formulae ).

%% The following rule specifies when a logic formula is in used-list

has_used_formula(State, Formula) :-
                 ob_prop_val(State, used, Formulae),
                 member(Formula, Formulae).

%% The following rule specifies when a relational formula is in relation-list

has_relational_formula(State, Rel_formula) :-
               ob_prop_val(State, relations, Rel_formulae),
               member(Rel_formula, Rel_formulae). 

%% The following rule is used to analyse a formula


consume_formula( State, Formula, NewState ):-
           ob_prop_val( State, available, FA ),
           ob_prop_val( State, used, FU ),
           select( Formula, FA, Rest ),
           set_ob_prop_val( State, available, Rest, NewState1 ),
           set_ob_prop_val( NewState1, used, [Formula | FU], NewState ).


/* 
add_formula_to_available( State, Formula, NewState ) :-
            ob_prop_val( State, available, FA ),
            set_ob_prop_val( State, available, [Formula | FA], NewState ).


*/



add_formula_to_available( State, Formula, NewState ) :-
            ob_prop_val( State, available, Available ),
            ( member(Formula, Available) ->  
              NewState = State
              ;   
              set_ob_prop_val( State, available, [Formula | Available], NewState )
            ), !.

add_formula_if_new(State, Formula, NewState ) :-
            ob_prop_val( State, used, Used ),
            ( member(Formula, Used) ->  
              NewState = State
              ;   
              add_formula_to_available( State, Formula, NewState )
            ), !.




add_rel_formula_to_relations(State, Rel_formula, NewState) :-
                             ob_prop_val(State, relations, Rel_formulae),
                             \+(member(Rel_formula, Rel_formulae)),
                             set_ob_prop_val(State, relations, [Rel_formula | Rel_formulae], NewState). 




%% ----------------  RULE FOR H-REFLEXIVITY --------------------
/*
refute(State, [h_reflexive | Rules]) :- 
       has_available_formula( State, S: (_)),
       add_rel_formula_to_relations(State, h(S,S), NewState1),
      %% \+(State = NewState1),
       !,
      applying(h_reflexive),
      print(newstate(NewState1)),
      refute(NewState1, Rules).

*/

%% -----------------RULES FOR CONTRADICTION ---------------------


refute( State, [contradiction] ):-
        has_available_formula( State, S:(Phi=t)),
        has_available_formula( State, S:(Phi=f)),
        applying(contradiction).


refute(State, [false_is_true]) :-
       has_available_formula(State, _S: (false = t)),
       applying(false_is_true).

%% -----------------NON-BRANCHING RULES and NON-CREATING ----------------------

%% Conjuction true 
%% Use add_formula_if_new to block the application of the rule if both 
%% the conclusions are in available formula or in used formula  

refute( State, [t_con | Rules] ):-
      consume_formula( State, S:(and(Phi,Psi)=t), NewState1 ),
      add_formula_if_new( NewState1, S:(Phi=t), NewState2 ),
      add_formula_if_new( NewState2, S:(Psi=t), Newstate3 ),
      !,
      applying(t_con),
      print(newstate(Newstate3)),
      refute( Newstate3, Rules ).

%% Disjunction false
%% Use add_formula_if_new to block the application of the rule if both 
%% the conclusions are in available formula or in used formula 

refute(State, [f_disj | Rules]) :-
      consume_formula(State, S: (or(Phi, Psi) = f), NewState1),
      add_formula_if_new(NewState1, S:(Phi = f), NewState2),
      add_formula_if_new(NewState2, S:(Psi = f), Newstate3),
      !,
      applying(f_disj),
      print(newstate(Newstate3)),
      refute(Newstate3, Rules). 

%% N-Negation true, Non-destructive rule

refute(State, [t_nneg | Rules]) :-
      has_available_formula(State, S:(nneg(Phi) = t )),
      has_relational_formula(State, h(S, T)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
      \+(State = NewState1),
      !,
      applying(t_nneg),
      print(newstate(NewState1)),
      refute(NewState1, Rules). 


%% E-Negation false, Non-destructive rule

refute(State, [f_eneg | Rules]) :-
      has_available_formula(State, S:(eneg(Phi) = f )),
      has_relational_formula(State, h(T, S)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(f_eneg),
      print(newstate(NewState1)),
      refute(NewState1, Rules).

%% White Box true, Non-destructive rule

refute(State, [t_wbox | Rules]) :-
      has_available_formula(State, S:(wbox(Phi) = t)),
      has_relational_formula(State, r(S, T)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(t_wbox),
      print(newstate(NewState1)),
      refute(NewState1, Rules).
 

 %% Black Diamond false, Non-destructive rule

refute(State, [f_bdia | Rules]) :-
      has_available_formula(State, S:(bdia(Phi) = f)),
      has_relational_formula(State, r(T, S)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
      \+(State = NewState1),
      !,
      applying(f_bdia),
      print(newstate(NewState1)),
      refute(NewState1, Rules).

%% Universal Box true, Non-destructive rule

refute(State, [t_ubox | Rules]) :-
      has_available_formula(State, _S:(ubox(Phi) = t)),
      has_available_formula( State, T: (_)),
      add_formula_if_new(State, T:(Phi = t), NewState1),
      \+(State = NewState1),
      !,
      applying(t_ubox),
      print(newstate(NewState1)),
      refute(NewState1, Rules).



%% Universal Diamond false, Non-destructive rule

refute(State, [f_udia | Rules]) :-
      has_available_formula(State, _S:(udia(Phi) = f)),
      has_available_formula( State, T: (_)),
      add_formula_if_new(State, T:(Phi = f), NewState1),
      \+(State = NewState1),
      !,
      applying(f_udia),
      print(newstate(NewState1)),
      refute(NewState1, Rules).




%% ---------------------- BRANCHING-RULES ------------------------------

%% True disjunction
refute( State, [t_dis, [t_dis_B1 | Rules1], [t_dis_B2 | Rules2] ] ) :-
        consume_formula( State, S:(or(Phi,Psi)=t), NewState1 ),
        add_formula_if_new(NewState1, S:(Phi=t), NewState2),
        add_formula_if_new(NewState1, S:(Psi = t), Newstate3),
        !,
        applying(t_dis),
        print(newstate_B1(NewState2)),
        print(newstate_B2(Newstate3)),
        refute(NewState2, Rules1), !,
        refute(Newstate3, Rules2). 


%% ----------------------- REFUTATION FAILS ------------------------------
%% if no rules are apllicable to a branch-state
%%fail the refutation process and print the state





refute( State, _ ) :- !, nl, nl,
      write( '!! CANNOT REFUTE !!' ), nl,
      write( '!! No rule applicable to the current formula set:'), nl,
      showlist_ind(State), nl, nl, !,
      fail.


%% This just prints out the elements of a list in a column format 
%% used to print elements of state list when open branch is found
%%
showlist_ind([]).
showlist_ind([H|T]) :- write('     '), write(H), nl, showlist_ind(T).



applying( Rule ):- write('Applying: '), write(Rule), nl.    


%% ------------------------------ TESTS ------------------------------

test_object( [available = [i:(and(p,p1)=t), i:(p1=f)], relations= [], used=[]] ).

test_object2( [available = [i: (and(p1, p2) = t)], used=[], relations = [h(i,i), h(i, j)] ] ).

test_object3( [available = [i: (nneg(p1) = t), w:(nneg(p1) = t) ], used=[], relations = [h(i, k)] ] ).

test_object4( [available = [i: (eneg(p1) = f)], used=[], relations = [h(i,i), h(j, i)] ] ).

test_object5( [available = [i: (wbox(p1) = t), i:(bdia(p2) = f)], used=[], relations = [r(i, j), r(i,i)] ] ).

test_object6( [available = [i: (bdia(p1) = f), i:(wbox(p1) = t )], used=[], relations = [r(i,i)] ] ).

test_object7( [available = [i: (ubox(p1) = t),  j:(udia(p1) = f )], used=[], relations = [] ] ).

test_object8( [available = [i: (ubox( and(p1, p2) ) = t)], used=[], relations = [] ] ).

test_object9( [available = [i: (udia( or(p1, p2) ) = f)], used=[], relations = [] ] ).

test_object10( [available = [ i:(or(p1,p2) = t), i:(p1 = f)], used=[], relations = [] ] ).

test_object11( [available = [i:(or(p1, or(p2, p3)) =t), i:(p1 = f), i:(p2 = f)], used=[], relations = [] ] ).




%% ----------------- ADD H-REFLEXIVITY LABELS---------------------

%% This predicate is a variation of list_of_labels: it takes into account also the labels appearing in the 
%% relation list.

list_of_labels2(S1, List) :-
                    ob_prop_val(S1, available, Available),
                    ob_prop_val(S1, relations, Relations),
                    possibly_empty_setof( Lab, (is_label_in(Lab, Available) ; is_label_in( Lab, Relations) ), List ), !.
                    


possibly_empty_setof( X, G, S) :- setof(X,G,S), !.
possibly_empty_setof( _, _, []).

%% predicate holding between a label and a list in which the label occurs

is_label_in( Label, Avail_or_Rel_List ) :- member( X, Avail_or_Rel_List), is_label_of(Label, X).


%% predicate holding between a label and the logic or relation formula that the label labels

is_label_of( Label, Logic_Formula ) :- Logic_Formula =  Label:(_), !.
is_label_of( Label, Relation_Formula ) :- Relation_Formula =.. [_, X, Y], (Label = X ; Label = Y).


%% this recursive predicate hold between a list of labels and the identity relation list 
%% on that list of labels 

list_H_reflexive([X], [h(X, X)]).

list_H_reflexive( [X |Rest], [h(X, X) | AddRest]) :- list_H_reflexive(Rest, AddRest), !. 



 %% This predicate is a variant of add_H_reflexive: it works with list_of_labels2
 %% and it adds to the relation list also the H-reflexivity on the labels that occur in the relation-list, and not in the available-list necessarily
 %% also, it adds the reflexivity of H to the relation list without deleting the relations that were present from the input
 %% we could use sort to eliminate the duplicate, say if for ex h(i,i) was there from the input(even if it shouldnt) we dont add it twice
 %% Indeed if we use set_ob_prop_val when we assume that we can start from a non-empty list of relations as input
 %% we would overwrite this list of relations with a new list -- the reflexivity of H only          

add_H_reflexive2(State, State_with_H_reflexive) :-
                 list_of_labels2(State, List_of_labels),
                 list_H_reflexive(List_of_labels, List_H_reflexive),
                 select(relations = Relations, State, Rest),
                 append(List_H_reflexive, Relations, UnionList_ofrelations),
                 sort(UnionList_ofrelations, UnionList_ofrelations1),
                 State_with_H_reflexive = [ relations = UnionList_ofrelations1 | Rest]. 



%%prove predicate refutes state with H reflexivity instead of just state. 
prove(State, Rules) :- 
      add_H_reflexive2(State, State_with_H_reflexive),
      refute(State_with_H_reflexive, Rules), !, nl, write('YES! REFUTATION ACCOMPLISHED!'). 


prove(_State, _Rules) :- write('NO! REFUTATION NOT ACCOMPLISHED: THERE IS OPEN BRANCH'), fail.



/*
%% this predicate holds between a state and the list of labels by which logic formulae are indexed
%% notice that the list "List" doesnt contain any repetion, thanks to the predicate sort. 

list_of_labels(S1, List) :-
                    ob_prop_val(S1, available, Available),
                    findall(Label, member(Label:(_), Available), List1),
                    sort(List1, List), !.         

                   
%% this recursive predicate hold between a list of labels and the identity relation list 
%% on that list of labels 

list_H_reflexive([X], [h(X, X)]).

list_H_reflexive( [X |Rest], [h(X, X) | AddRest]) :- list_H_reflexive(Rest, AddRest), !. 


%% this predicate holds between a state and another state where the latter is the same as the former 
%% but its list of relations include H(X, X) for every X in labels. NB relation-list of state has to be empty
%% otherrwise it just gets overwritten due to set_ob_prop_val. 

 add_H_reflexive(State, State_with_H_reflexive) :-
                 list_of_labels(State, List_of_labels),
                 list_H_reflexive(List_of_labels, List_H_reflexive),
                 set_ob_prop_val(State, relations, List_H_reflexive, State_with_H_reflexive). 
*/


