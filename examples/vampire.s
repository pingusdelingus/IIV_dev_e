%------------------------------------------------------------------------------
tff(semantics,logic,
    $alethic_modal ==
      [ $domains == $constant,
        $designation == $rigid,
        $terms == $local,
        $modalities == $modal_system_M ] ).

%----Declarations to fool Vampire when processing this file directly
% tff('$world_type',type,$world: $tType).
% tff('$local_world_decl',type,$local_world: $world).
% tff('$accessible_world_decl',type,$accessible_world: ($world * $world) > $o).

tff(person_decl,type,    person: $tType).
tff(product_decl,type,   product: $tType).
tff(alex_decl,type,      alex: person).
tff(chris_decl,type,     chris: person).
tff(leo_decl,type,       leo: product).
tff(work_hard_decl,type, work_hard: (person * product) > $o).
tff(gets_rich_decl,type, gets_rich: person > $o).

tff(d_person_type,type,  d_person: $tType).
tff(d2person_decl,type,  d2person: d_person > person ).
tff(d_alex_decl,type,    d_alex: d_person).
tff(d_chris_decl,type,   d_chris: d_person).
tff(d_product_type,type, d_product: $tType).
tff(d2product_decl,type, d2product: d_product > product ).
tff(d_leo_decl,type,     d_leo: d_product).

tff(w1_decl,type,w1:     $world).
tff(w2_decl,type,w2:     $world).

tff(leo_workers_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = w1 | W = w2 )
    & $distinct(w1,w2)
    & $local_world = w2
    & $accessible_world(w1,w1)     %----Logic is M
    & $accessible_world(w2,w2)
    & $accessible_world(w1,w2)
    & $accessible_world(w2,w1) ) ). 

tff(leo_workers_domains,interpretation-domains,
    ( $in_world(w1,
        ( ( ! [P: person] : ? [DP: d_person] : P = d2person(DP)
          & ! [DP: d_person] : ( DP = d_alex | DP = d_chris )
          & $distinct(d_alex,d_chris)
          & ? [DP: d_person] : ( DP = d_alex )
          & ? [DP: d_person] : ( DP = d_chris )
          & ! [DP1: d_person,DP2: d_person] : 
              ( d2person(DP1) = d2person(DP2) => DP1 = DP2 ) )
        & ( ! [P: product] : ? [DP: d_product] : P = d2product(DP)
          & ! [DP: d_product] : DP = d_leo
          & ? [DP: d_product] : DP = d_leo
          & ! [DP1: d_product,DP2: d_product] :
              ( d2product(DP1) = d2product(DP2) => DP1 = DP2 ) ) ))
    & $in_world(w2,
        ( ( ! [P: person] : ? [DP: d_person] : P = d2person(DP)
          & ! [DP: d_person] : ( DP = d_alex | DP = d_chris )
          & $distinct(d_alex,d_chris)
          & ? [DP: d_person] : ( DP = d_alex )
          & ? [DP: d_person] : ( DP = d_chris )
          & ! [DP1: d_person,DP2: d_person] : 
              ( d2person(DP1) = d2person(DP2) => DP1 = DP2 ) )
        & ( ! [P: product] : ? [DP: d_product] : P = d2product(DP)
          & ! [DP: d_product] : DP = d_leo
          & ? [DP: d_product] : DP = d_leo
          & ! [DP1: d_product,DP2: d_product] :
              ( d2product(DP1) = d2product(DP2) => DP1 = DP2 ) ) )) ) ).

tff(leo_workers_mappings,interpretation-mappings,
    ( $in_world(w1,
        ( ( alex = d2person(d_alex)
          & chris = d2person(d_chris)
          & leo = d2product(d_leo) )
        & ( work_hard(d2person(d_alex),d2product(d_leo))
          & work_hard(d2person(d_chris),d2product(d_leo))
          & gets_rich(d2person(d_alex))
          & gets_rich(d2person(d_chris)) ) ))
    & $in_world(w2,
        ( ( alex = d2person(d_alex)
          & chris = d2person(d_chris)
          & leo = d2product(d_leo) )
        & ( work_hard(d2person(d_alex),d2product(d_leo))
          & work_hard(d2person(d_chris),d2product(d_leo))
          & ~ gets_rich(d2person(d_alex))
          & ~ gets_rich(d2person(d_chris)) ) )) ) ). 
%------------------------------------------------------------------------------
