tff('s4_path_n.0001', logic, ($modal) == ([($modalities) == ($modal_system_S4)])).


tff(false_decl, type, false: $o).
tff(p11_decl, type, p11: $o).
tff(p12_decl, type, p12: $o).
tff(p13_decl, type, p13: $o).
tff(p14_decl, type, p14: $o).
tff(p15_decl, type, p15: $o).
tff(p16_decl, type, p16: $o).
tff(p21_decl, type, p21: $o).
tff(p22_decl, type, p22: $o).
tff(p23_decl, type, p23: $o).
tff(p24_decl, type, p24: $o).
tff(p25_decl, type, p25: $o).
tff(p26_decl, type, p26: $o).


tff(world_0_decl, type, world_0: $world).
tff(world_1_decl, type, world_1: $world).
tff(world_2_decl, type, world_2: $world).

tff(model_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = world_0 | W = world_1 | W = world_2 )
    & $distinct(world_0, world_1, world_2)
    & $local_world = world_2
    & $accessible_world(world_0,world_0)
    & $accessible_world(world_0,world_1)
    & $accessible_world(world_0,world_2)
    & $accessible_world(world_1,world_0)
    & $accessible_world(world_1,world_1)
    & $accessible_world(world_1,world_2)
    & $accessible_world(world_2,world_0)
    & $accessible_world(world_2,world_1)
    & $accessible_world(world_2,world_2)
    ) ).
tff(model_mapping, interpretation-mappings,
($in_world(world_0,
	(~false
	& ~p11
	& ~p12
	& ~p13
	& p14
	& ~p15
	& p16
	& ~p21
	& p22
	& ~p23
	& p24
	& p25
	& p26))
& $in_world(world_1,
	(~false
	& ~p11
	& ~p12
	& ~p13
	& p14
	& ~p15
	& p16
	& ~p21
	& p22
	& ~p23
	& p24
	& p25
	& p26))
& $in_world(world_2,
	(~false
	& ~p11
	& ~p12
	& ~p13
	& p14
	& ~p15
	& p16
	& ~p21
	& p22
	& ~p23
	& p24
	& p25
	& p26))
)).