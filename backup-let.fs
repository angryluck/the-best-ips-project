        | Let (Dec (name, def, decpos), body, pos) ->
          let existing_variable = SymTab.lookup name vtable
          match existing_variable with 
            | Some _ -> 
                // If 'name' already in vtable, no optimization (easy way out)
                Let (Dec (name, def, decpos), body, pos)
            | None -> 
                let def' = copyConstPropFoldExp vtable def
                match def' with
                    | Var (var_name, pos) ->
                        let vtable' = SymTab.bind name (VarProp var_name) vtable
                        copyConstPropFoldExp vtable' body
                    (* TODO project task 3:
                        Hint: I have discovered a variable-copy statement `let x = a`.
                              I should probably record it in the `vtable` by
                              associating `x` with a variable-propagatee binding,
                              and optimize the `body` of the let.
                    *)
                    | Constant (value, pos) ->
                        let vtable' = SymTab.bind name (ConstProp value) vtable
                        copyConstPropFoldExp vtable' body
                    (* TODO project task 3:
                        Hint: I have discovered a constant-copy statement `let x = 5`.
                              I should probably record it in the `vtable` by
                              associating `x` with a constant-propagatee binding,
                              and optimize the `body` of the let.
                    *)
                    | Let (Dec (name2, def2, decpos2), body2, pos2) ->
                    // let name2 = addUniqueSuffix(name2)
                        let last_let = Let (Dec (name, body2, pos2), body, pos)
                        let full_let = Let (Dec (name2, def2, decpos2), last_let, pos)
                        copyConstPropFoldExp vtable full_let
                        // Let (Dec (name2, def2, decpos2), last_let, pos)
                    // let exp = Let (Dec (name2, def2, decpos2), )
                    // let def2' = copyConstPropFoldExp vtable def2
                    // Before:
                    // let name = (let name2 = def2 in body2) in body
                    // After:
                    // let name2 = def2 in  let name = body2 in body


                    (* TODO project task 3:
                        Hint: this has the structure
                                `let y = (let x = e1 in e2) in e3`
                        Problem is, in this form, `e2` may simplify
                        to a variable or constant, but I will miss
                        identifying the resulting variable/constant-copy
                        statement on `y`.
                        A potential solution is to optimize directly the
                        restructured, semantically-equivalent expression:
                                `let x = e1 in let y = e2 in e3`
                        but beware that x might also occur in e3, in the
                        original expression.
                    *)
                    // failwith "Unimplemented copyConstPropFold for Let with Let"
                    | _ -> (* Fallthrough - for everything else, do nothing *)
                        let body' = copyConstPropFoldExp vtable body
                        Let (Dec (name, def', decpos), body', pos)

 
