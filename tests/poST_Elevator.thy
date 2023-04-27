theory poST_Elevator
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin

definition Elevator :: "model" where
"Elevator = 
  (None,[],
  [(''Controller'',
    [(prog_var.InVar 
      ( 
        [(''onfloor0'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''onfloor1'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''onfloor2'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call0'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call1'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call2'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button0'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button1'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button2'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''door0closed'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''door1closed'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''door2closed'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])),
     (prog_var.OutVar 
      ( 
        [(''up'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''down'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''open0'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''open1'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''open2'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call0_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call1_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''call2_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button0_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button1_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''button2_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''floor0_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''floor1_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''floor2_LED'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
         (''cur'',var_init_decl.Symbolic (basic_post_type.Int 0) None)])),
     (prog_var.Var (False, 
      ( 
        [(''target'',var_init_decl.Symbolic (basic_post_type.Int 0) None)])))],
    [(''Init'',
      [],
      [(''begin'',
        False,
        [(statement.ProcessSt (process_contextment.Start (Some ''Call0Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''Call1Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''Call2Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''Button0Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''Button1Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''Button2Latch''))),
         (statement.ProcessSt (process_contextment.Start (Some ''CheckCurFloor''))),
         (statement.ProcessSt (process_contextment.Start (Some ''UpControl''))),
         (statement.ProcessSt (process_contextment.Stop None))],
        None)::state_decl])::process_decl,
     (''Call0Latch'',
      [(proc_var.Var (False,
        ([(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') (expr.Unary unary_op.Not (expr.SymbolicVar ''call0''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') (expr.Unary unary_op.Not (expr.SymbolicVar ''open0''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''call0'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call0_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open0'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call0_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''call0'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open0''))],
        None)]),
     (''Call1Latch'',
      [(proc_var.Var (False,
        (
          [(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''call1''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''open1''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''call1'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call1_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open1'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call1_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''call1'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open1''))],
        None)]),
     (''Call2Latch'',
      [(proc_var.Var (False,
        (
          [(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''call2''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''open2''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''call2'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call2_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open2'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call2_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''call2'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open2''))],
        None)]),
     (''Button0Latch'',
      [(proc_var.Var (False,
        (
          [(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''button0''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''open0''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''button0'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button0_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open0'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button0_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''button0'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open0''))],
        None)]),
     (''Button1Latch'',
      [(proc_var.Var (False,
        (
          [(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''button1''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''open1''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''button1'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button1_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open1'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button1_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''button1'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open1''))],
        None)]),
     (''Button2Latch'',
      [(proc_var.Var (False,
        ([(''prev_in'',var_init_decl.Symbolic (basic_post_type.Bool False) None),
           (''prev_out'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''button2''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.Unary unary_op.Not (expr.SymbolicVar ''open2''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''button2'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button2_LED'') ( expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open2'') (expr.Unary unary_op.Not (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''button2_LED'') ( expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'') ( expr.SymbolicVar ''button2'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'') ( expr.SymbolicVar ''open2''))],
        None)]),
     (''CheckCurFloor'',
      [],
      [(''check_floor'',
        False,
        [(statement.SelectSt (select_statement.IfSt 
                                [(expr.SymbolicVar ''onfloor0'',
                                  [(statement.AssignSt (common_var.Symbolic ''floor0_LED'') ( expr.Const (const.Bool True))),
                                   (statement.AssignSt (common_var.Symbolic ''floor1_LED'') ( expr.Const (const.Bool False))),
                                   (statement.AssignSt (common_var.Symbolic ''floor2_LED'') ( expr.Const (const.Bool False)))]),
                                 (expr.SymbolicVar ''onfloor1'',
                                  [(statement.AssignSt (common_var.Symbolic ''floor0_LED'') ( expr.Const (const.Bool False))),
                                   (statement.AssignSt (common_var.Symbolic ''floor1_LED'') ( expr.Const (const.Bool True))),
                                   (statement.AssignSt (common_var.Symbolic ''floor2_LED'') ( expr.Const (const.Bool False)))]),
                                 (expr.SymbolicVar ''onfloor2'',
                                  [(statement.AssignSt (common_var.Symbolic ''floor0_LED'') ( expr.Const (const.Bool False))),
                                   (statement.AssignSt (common_var.Symbolic ''floor1_LED'') ( expr.Const (const.Bool False))),
                                   (statement.AssignSt (common_var.Symbolic ''floor2_LED'') ( expr.Const (const.Bool True)))])]
                                None))],
        None)]),
     (''UpControl'',
      [],
      [(''check_calls'',
        False,
        [statement.SelectSt (select_statement.IfSt
                              [(expr.Binary (binary_op.Or)
                                    (expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 0)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call0_LED'') (expr.SymbolicVar ''button0_LED'')))
                                  (expr.Binary (binary_op.Or)
                                     ((expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 1)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call1_LED'') (expr.SymbolicVar ''button1_LED''))))
                                     ((expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 2)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call2_LED'') (expr.SymbolicVar ''button2_LED''))))),
                                  [(statement.ProcessSt (process_contextment.Start (Some ''DoorCycle''))),
                                   (statement.SetStateSt (Some ''door_cycle''))])]
                              (Some
                                [(statement.SelectSt (select_statement.CaseSt
                                    (expr.SymbolicVar ''cur'')
                                    [([0],
                                        [(statement.SelectSt (select_statement.IfSt
                                            [(expr.Binary (binary_op.Or)
                                                (expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call1_LED'')
                                                  (expr.SymbolicVar ''button1_LED''))
                                                ((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call2_LED'')
                                                  (expr.SymbolicVar ''button2_LED''))),
                                              [(statement.ProcessSt (process_contextment.Start (Some ''UpMotion''))),
                                               (statement.SetStateSt None)])]
                                            None))]),
                                     ([1],
                                        [(statement.SelectSt (select_statement.IfSt
                                            [((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call2_LED'')
                                                  (expr.SymbolicVar ''button2_LED'')),
                                               [(statement.ProcessSt (process_contextment.Start (Some ''UpMotion''))),
                                                (statement.SetStateSt None)]),
                                             ((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call0_LED'')
                                                  (expr.SymbolicVar ''button0_LED'')),
                                               [(statement.ProcessSt (process_contextment.Start (Some ''DownControl''))),
                                                (statement.ProcessSt (process_contextment.Stop None))])]
                                            None))]),
                                     ([2],[(statement.ProcessSt (process_contextment.Start (Some ''DownControl''))),
                                           (statement.ProcessSt (process_contextment.Stop None))])]
                                    None))]))],
        None),
       (''check_stop'',
        False,
        [(statement.SelectSt (select_statement.IfSt
            [((expr.ProcStatEpxr ''UpMotion'' proc_status.Inactive),
              [(statement.ProcessSt (process_contextment.Start (Some ''DoorCycle''))),
               (statement.SetStateSt None)])]
            None))],
        None),
       (''door_cycle'',
        False,
        [(statement.SelectSt (select_statement.IfSt
            [((expr.ProcStatEpxr ''DoorCycle'' proc_status.Inactive),
              [(statement.ProcessSt (process_contextment.Start None))])]
            None))],
        None)]),
     (''UpMotion'',
      [],
      [(''start'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''up'') (expr.Const (const.Bool True))),
         (statement.SelectSt (select_statement.CaseSt
          (expr.SymbolicVar ''cur'')
          [([0],
              [(statement.SelectSt (select_statement.IfSt
                [((expr.Binary (binary_op.Or)
                      (expr.SymbolicVar ''call1_LED'')
                      (expr.SymbolicVar ''button1_LED'')),
                    [(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 1))),
                     (statement.SetStateSt None)])]
                None))]),
           ([1],
              [(statement.SelectSt (select_statement.IfSt
                [((expr.Binary (binary_op.Or)
                    (expr.SymbolicVar ''call2_LED'')
                    (expr.SymbolicVar ''button2_LED'')),
                      [(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 2))),
                       (statement.SetStateSt None)])]
                None))]),
           ([2],[(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 2))),
                 (statement.SetStateSt None)])]
           None))],
        None),
       (''check_target'',
        False,
        [(statement.SelectSt (select_statement.IfSt
           [((expr.Binary binary_op.Eq
                (expr.SymbolicVar ''up'')
                (expr.SymbolicVar ''target'')),
              [(statement.AssignSt (common_var.Symbolic ''up'') (expr.Const (const.Bool False))),
               (statement.ProcessSt (process_contextment.Stop None))])]
           None))],
        None) ]),
     (''UpControl'',
      [],
      [(''check_calls'',
        False,
        [statement.SelectSt (select_statement.IfSt
                              [(expr.Binary (binary_op.Or)
                                    (expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 0)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call0_LED'') (expr.SymbolicVar ''button0_LED'')))
                                  (expr.Binary (binary_op.Or)
                                     ((expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 1)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call1_LED'') (expr.SymbolicVar ''button1_LED''))))
                                     ((expr.Binary (binary_op.And)
                                       (expr.Binary (binary_op.Eq) (expr.SymbolicVar ''cur'') (expr.Const (const.Int 2)))
                                       (expr.Binary (binary_op.Or) (expr.SymbolicVar ''call2_LED'') (expr.SymbolicVar ''button2_LED''))))),
                                  [(statement.ProcessSt (process_contextment.Start (Some ''DoorCycle''))),
                                   (statement.SetStateSt (Some ''door_cycle''))])]
                              (Some
                                [(statement.SelectSt (select_statement.CaseSt
                                    (expr.SymbolicVar ''cur'')
                                    [([0],[(statement.ProcessSt (process_contextment.Start (Some ''UpControl''))),
                                           (statement.ProcessSt (process_contextment.Stop None))]),
                                     ([1],
                                        [(statement.SelectSt (select_statement.IfSt
                                            [((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call0_LED'')
                                                  (expr.SymbolicVar ''button0_LED'')),
                                               [(statement.ProcessSt (process_contextment.Start (Some ''DownMotion''))),
                                                (statement.SetStateSt None)]),
                                             ((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call2_LED'')
                                                  (expr.SymbolicVar ''button2_LED'')),
                                               [(statement.ProcessSt (process_contextment.Start (Some ''UpControl''))),
                                                (statement.ProcessSt (process_contextment.Stop None))])]
                                            None))]),
                                     ([2],
                                        [(statement.SelectSt (select_statement.IfSt
                                            [(expr.Binary (binary_op.Or)
                                                (expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call1_LED'')
                                                  (expr.SymbolicVar ''button1_LED''))
                                                ((expr.Binary (binary_op.Or)
                                                  (expr.SymbolicVar ''call0_LED'')
                                                  (expr.SymbolicVar ''button0_LED''))),
                                              [(statement.ProcessSt (process_contextment.Start (Some ''DownMotion''))),
                                               (statement.SetStateSt None)])]
                                            None))])]
                                    None))]))],
        None),
       (''check_stop'',
        False,
        [(statement.SelectSt (select_statement.IfSt
            [((expr.ProcStatEpxr ''DownMotion'' proc_status.Inactive),
              [(statement.ProcessSt (process_contextment.Start (Some ''DoorCycle''))),
               (statement.SetStateSt None)])]
            None))],
        None),
       (''door_cycle'',
        False,
        [(statement.SelectSt (select_statement.IfSt
            [((expr.ProcStatEpxr ''DoorCycle'' proc_status.Inactive),
              [(statement.ProcessSt (process_contextment.Start None))])]
            None))],
        None)]),
     (''DownMotion'',
      [],
      [(''start'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''down'') (expr.Const (const.Bool True))),
         (statement.SelectSt (select_statement.CaseSt
          (expr.SymbolicVar ''cur'')
          [([0],[(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 0))),
                 (statement.SetStateSt None)]),
           ([1],
              [(statement.SelectSt (select_statement.IfSt
                [((expr.Binary (binary_op.Or)
                    (expr.SymbolicVar ''call0_LED'')
                    (expr.SymbolicVar ''button0_LED'')),
                      [(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 0))),
                       (statement.SetStateSt None)])]
                None))]),
           ([2],
              [(statement.SelectSt (select_statement.IfSt
                [((expr.Binary (binary_op.Or)
                      (expr.SymbolicVar ''call1_LED'')
                      (expr.SymbolicVar ''button1_LED'')),
                    [(statement.AssignSt (common_var.Symbolic ''target'') (expr.Const (const.Int 1))),
                     (statement.SetStateSt None)])]
                None))])]
           None))],
        None),
       (''check_target'',
        False,
        [(statement.SelectSt (select_statement.IfSt
           [((expr.Binary binary_op.Eq
                (expr.SymbolicVar ''up'')
                (expr.SymbolicVar ''target'')),
              [(statement.AssignSt (common_var.Symbolic ''down'') (expr.Const (const.Bool False))),
               (statement.ProcessSt (process_contextment.Stop None))])]
           None))],
        None) ]),
     (''DoorCycle'',
      [],
      [(''choose_door_to_open'',
        False,
        [(statement.SelectSt (select_statement.CaseSt
            (expr.SymbolicVar ''cur'')
            [([0],
                [(statement.AssignSt (common_var.Symbolic ''open0'') (expr.Const (const.Bool True)))]),
             ([1],
                [(statement.AssignSt (common_var.Symbolic ''open1'') (expr.Const (const.Bool True)))]),
             ([2],
                [(statement.AssignSt (common_var.Symbolic ''open2'') (expr.Const (const.Bool True)))])]
            None)),
         (statement.SetStateSt None)],
        None),
       (''delay3s'',
        False,
        [],
        (Some (timeout_statement.Const (const.Time (time.Time 0 0 0 3 0))
          [(statement.AssignSt (common_var.Symbolic ''open0'') (expr.Const (const.Bool False))),
           (statement.AssignSt (common_var.Symbolic ''open1'') (expr.Const (const.Bool False))),
           (statement.AssignSt (common_var.Symbolic ''open2'') (expr.Const (const.Bool False))),
           (statement.SetStateSt None)]))),
       (''check_closed'',
        False,
        [(statement.SelectSt (select_statement.IfSt
            [((expr.Binary binary_op.And
                (expr.Binary binary_op.And
                  (expr.SymbolicVar ''door0closed'')
                  (expr.SymbolicVar ''door1closed''))
                (expr.SymbolicVar ''door2closed'')),
              [(statement.ProcessSt (process_contextment.Stop None))])]
            None))],
        None)])
])::program_decl],
  [],[])"

end