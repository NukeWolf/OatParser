open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for
     compiling local variable declarations
*)

type elt =
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None ->
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator"
    | Some term ->
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None

end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) ->
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.


   Consider globals7.oat

   /--------------- globals7.oat ------------------
   global arr = int[] null;

   int foo() {
     var x = new int[3];
     arr = x;
     x[2] = 3;
     return arr[2];
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has
       the same type as @arr

   (2) @oat_alloc_array allocates len+1 i64's

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7

   (4) stores the resulting array value (itself a pointer) into %_x7

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed
      to by %_x7

  (6) store the array value (a pointer) into @arr

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] },
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr

  (11)  calculate the array index offset

  (12) load the array value at the index

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* )
  @_global_arr5 = global { i64, [4 x i64] }
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*)

(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the stack, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate an array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

let str_arr_ty s = Array(1 + String.length s, I8)


(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression.

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to bitcast the
     resulting gid to (Ptr I8)

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

   - we found it useful to write a helper function
     cmp_exp_as : Ctxt.t -> Ast.exp node -> Ll.ty -> Ll.operand * stream
     that compiles an expression and optionally inserts a bitcast to the
     desired Ll type. This is useful for dealing with OAT identifiers that
     correspond to gids that don't quite have the type you want

*)


let ast_binop_to_ll_insn (ast_binop : Ast.binop) (res_ty: Ll.ty) (op1_ty:Ll.ty) (op1:Ll.operand) (op2:Ll.operand): Ll.insn =
  match ast_binop with 
    | Add -> Binop (Add,res_ty,op1,op2)
    | Mul -> Binop (Mul,res_ty,op1,op2)
    | Sub -> Binop (Sub,res_ty,op1,op2)
    | Shl -> Binop (Shl,res_ty,op1,op2)
    | Shr -> Binop (Lshr,res_ty,op1,op2)
    | Sar -> Binop (Ashr,res_ty,op1,op2)
    | IAnd -> Binop (And,res_ty,op1,op2)
    | IOr ->  Binop (Or,res_ty,op1,op2)
    | Eq -> Icmp (Eq,op1_ty,op1,op2)
    | Neq -> Icmp (Ne,op1_ty,op1,op2)
    | Lt -> Icmp (Slt,op1_ty,op1,op2)
    | Lte -> Icmp (Sle,op1_ty,op1,op2)
    | Gt -> Icmp (Sgt,op1_ty,op1,op2)
    | Gte -> Icmp (Sge,op1_ty,op1,op2)
    | And -> Binop (And,res_ty,op1,op2)
    | Or -> Binop (Or,res_ty,op1,op2)

let ast_unop_to_ll_insn (ast_unop : Ast.unop) (res_ty: Ll.ty) (op_ty:Ll.ty) (op:Ll.operand): Ll.insn =
  match ast_unop with 
    | Neg -> Binop(Mul, res_ty, op, Const(-1L))
    | Bitnot -> Binop(Xor, res_ty, op, Const (-1L))
    | Lognot  -> Binop(Xor, res_ty, op, Const (1L))


let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  let cmp_exp_as (c:Ctxt.t) (exp:Ast.exp node) (newty : Ll.ty) : Ll.operand * stream = 
    let llty,llop,stream = cmp_exp c exp in 
    if (llty == newty) then
      llop,stream
    else
      let newOp = gensym "bitcast" in
      Id newOp, stream >@ [I( newOp , Bitcast (llty, llop, newty))]

  in
  match exp.elt with
  | Ast.CInt i  -> I64, Const i, []
  | Ast.CNull t -> cmp_ty (Ast.TRef t), Null, []
  | Ast.Call (f, es) -> cmp_call c f es

  | Ast.CStr str -> 
    let gid = gensym "str" in
    let raw_gid = gensym "raw_str" in
    let local_str = gensym "local_str" in
    let ll_ty = str_arr_ty str in
    let cast = GBitcast (Ptr ll_ty, GGid raw_gid, Ptr I8) in
    Ptr I8, Id local_str, [
      I (local_str, Load (Ptr(Ptr(I8)), Gid gid));
      G (gid, (Ptr I8, cast));
      G (raw_gid, (ll_ty, GString str))
      ]


  | Ast.CArr (ty, elements) -> 
    let arr_ty, arr_op, arr_stream = oat_alloc_array ty (Const (Int64.of_int (List.length elements))) in
    let arr_fill_stream,_ = List.fold_left (fun (acc_stream, ind:stream * int) (exp: Ast.exp node) ->
        let exp_ty, exp_op, exp_stream = cmp_exp c exp in
        let elm_ptr_op = gensym "ptr" in
        acc_stream >@ exp_stream >@ [
          I(gensym "store", Store((cmp_ty ty), exp_op, Id elm_ptr_op));
          I(elm_ptr_op, Gep (arr_ty, arr_op, [Const 0L; Const 1L; Const (Int64.of_int ind)]))
        ], (ind + 1)
      )
      ([],0)
      elements
    in
    arr_ty, arr_op, arr_stream >@ arr_fill_stream
  | Ast.Index (arr, index) -> 
    let index_ty, index_op, index_stream = cmp_exp c index in
    let arr_ty, arr_op, arr_stream = cmp_exp c arr in
    let val_ty = match arr_ty with 
      | Ptr (Struct([_; Array( _, ty)])) -> ty
      | _ -> failwith (string_of_ty arr_ty)
    in
    let res_op_ptr = gensym "arr_index_ptr" in
    let res_op = gensym "arr_val" in 
    val_ty, Id res_op, index_stream >@ arr_stream >@ [
      I(res_op, Load(Ptr(val_ty), Id res_op_ptr));
      I(res_op_ptr, Gep (arr_ty, arr_op, [Const 0L; Const 1L; index_op]))
    ]
  
  | Ast.NewArr (ty, len_exp) ->
    let exp_ty, exp_op, exp_stream = cmp_exp c len_exp in
    let arr_ty, arr_op, arr_stream = oat_alloc_array ty exp_op in
    arr_ty, arr_op, exp_stream >@ arr_stream

  | Ast.CBool true -> I1, Const 1L, []
  | Ast.CBool false -> I1, Const 0L, []
  | Ast.Bop (binop,exp1,exp2) -> 
    let binop_types = typ_of_binop binop in
    let exp1_ty,exp2_ty,res_ty = binop_types in
    let exp1_op, exp1_stream = cmp_exp_as c exp1 (cmp_ty exp1_ty) in
    let exp2_op, exp2_stream = cmp_exp_as c exp2 (cmp_ty exp2_ty) in
    let res_op = gensym (Astlib.ml_string_of_binop binop) in
    (cmp_ty res_ty), Id res_op , 
    ([I(res_op, (ast_binop_to_ll_insn binop (cmp_ty res_ty) (cmp_ty exp1_ty) exp1_op exp2_op ))] 
    @ exp2_stream @ exp1_stream)

  | Ast.Uop (unop, exp) ->
    let unop_types = typ_of_unop unop in
    let exp_ty,res_ty = unop_types in
    let exp1_op, exp1_stream = cmp_exp_as c exp (cmp_ty exp_ty) in
    let res_op = gensym (Astlib.ml_string_of_unop unop) in
    (cmp_ty res_ty), Id res_op,
    exp1_stream >@ [I(res_op, (ast_unop_to_ll_insn unop (cmp_ty res_ty) (cmp_ty exp_ty) exp1_op))]
    
  | Ast.Id id -> 
    let ty, op = (Ctxt.lookup id c) in
    let res_op = gensym "load_id" in 
    (* Printf.printf "%s" id; *)
    begin match ty with
      | Ptr (newty) -> newty, Id res_op , [I(res_op, Load (ty, op))]
      | _ -> ty, op, []
      (* | _ -> failwith "Load function expected a pointer or id" *)
    end
    
  | _ -> failwith "The rest of cmp_exp unimplemented"

and cmp_call (c:Ctxt.t) (exp:Ast.exp node) (es:Ast.exp node list) : Ll.ty * Ll.operand * stream =
  let fun_id = match exp.elt with 
                | Id id -> id
                | _ -> failwith "given exp node is not an id"
  in
  let ty, op = Ctxt.lookup_function fun_id c in
  let res_op = gensym "function_result" in 
  let args_fold_helper = fun (acc_operands, acc_stream : (Ll.ty * Ll.operand) list * stream) (arg_exp:Ast.exp node) ->
    let ty, op, stream = cmp_exp c arg_exp in
    acc_operands @ [(ty,op)] , stream >@ acc_stream
  in
  let arg_list, arg_stream = List.fold_left args_fold_helper ([],[]) es in
  match ty with 
    | Ptr(Fun (args, ret)) -> (ret, Id res_op , arg_stream >@ [I(res_op, Call(ret, op, arg_list))])
    | _ -> failwith "Gid not attributed to a function pointer"
  

(* Feel free to add more recursive functions here *)


(* Compile a statement in context c with return typ rt. Return a new context,
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Ret None -> c, [T (Ret (rt, None))]
  | Ret (Some x) ->
    let compiled_exp = cmp_exp c x in
    let ty, op, stream = compiled_exp in
    c,  [T (Ret (rt, Some op))] @ stream
  | Assn (lhs, exp) ->
    (* lhs = exp; *)
    begin match lhs.elt with
      | Id id ->
        let ty, op, stream = cmp_exp c exp in
        let lhs_ty, lhs_op = Ctxt.lookup id c in
        c, stream >@ [I (gensym id, Store (ty, op, lhs_op))]
      | Index (arr, i) -> 
        let ty, op, stream = cmp_exp c exp in
        let index_ty, index_op, index_stream = cmp_exp c i in
        let arr_ty, arr_op, arr_stream = cmp_exp c arr in
        let res_op_ptr = gensym "arr_index_ptr" in
        let res_op = gensym "arr_val" in 
        c, stream >@ index_stream >@ arr_stream >@ [
        I(res_op, Store(ty, op , Id res_op_ptr));
        I(res_op_ptr, Gep (arr_ty, arr_op, [Const 0L; Const 1L; index_op]))
    ]
      | _ -> failwith "program is not well-formed"
    end
  | Decl (id, exp) ->
    (* var id = exp; *)
    let ty, op, stream = cmp_exp c exp in
    let uid = gensym id in
    let uid2 = gensym id in (* TODO is this necessary? *)
    let new_ctxt = Ctxt.add c id (Ptr ty, Id uid) in
    (* you will need to emit Allocas in the
     entry block of the current function using the E() constructor *)
    let alloca = [E (uid, Alloca ty)] in
    new_ctxt, alloca >@ stream >@ [I (uid2, Store (ty, op, Id uid))]
  | SCall (id, es) -> 
    let _, _, stream = cmp_exp c (Ast.no_loc (Ast.Call(id,es))) in
    c, stream

  | If (exp, block, else_stmt) ->
    let ty, op, stream = cmp_exp c exp in
    let true_body = cmp_block c rt block in
    let false_body = cmp_block c rt else_stmt in

    let true_label = gensym "true_label" in
    let false_label = gensym "false_label" in
    let end_false_label = gensym "end_false_label" in

    (c,
      stream >@

      [T (Cbr (op, true_label, false_label))] >@

      [L true_label] >@
      true_body >@
      [T (Br end_false_label)] >@

      [L false_label] >@
      false_body >@
      [T (Br end_false_label)] >@

      [L end_false_label]
    )
  | For (vdecls, expopt, stmtopt, block) -> 
    let for_check_label = gensym "for_check_label" in
    let for_body_label = gensym "for_body_label" in
    let for_end_label = gensym "for_end_label" in

    let var_stream_helper = fun (acc_c, acc_stream : Ctxt.t * stream) (vd:Ast.vdecl) -> 
      let new_c, new_stream = (cmp_stmt acc_c Ll.Void {elt=Decl(vd); loc=Range.norange}) in
      new_c, acc_stream >@ new_stream
    in
    let decl_ctxt, decl_stream = List.fold_left var_stream_helper (c,[]) vdecls in

    let exp_stream = match expopt with 
      | Some (exp) -> 
        let ty,op,stream = cmp_exp decl_ctxt exp in
        stream >@
        [T (Cbr (op, for_body_label, for_end_label))]
      | None ->  
        [T (Br for_body_label)]
    in
    let body_stream = cmp_block decl_ctxt rt block in
    let for_action_ctxt, for_action_stream = match stmtopt with
      | Some (stmt) -> cmp_stmt decl_ctxt rt stmt
      | None -> decl_ctxt, []
    in
 
    (for_action_ctxt,
      decl_stream >@
      [T (Br for_check_label)] >@
      [L for_check_label] >@
      exp_stream >@

      [L for_body_label] >@
      body_stream >@
      for_action_stream >@
      [T (Br for_check_label)] >@

      [L for_end_label] 
      )
  | While (exp, block) ->
    let ty, op, stream = cmp_exp c exp in
    let while_body = cmp_block c rt block in
    let start_while_label = gensym "start_while_label" in
    let end_while_label = gensym "end_while_label" in
    let start_while_body_label = gensym "start_while_body_label" in

    (c,
      [T (Br start_while_label)] >@
      [L start_while_label] >@
      stream >@ 
      [T (Cbr (op, start_while_body_label, end_while_label))] >@ 

      [L start_while_body_label] >@ 
      while_body >@ 
      [T (Br start_while_label)] >@

      [L end_while_label]
    )


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : stream =
  snd @@ List.fold_left (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p

(* Populate a context with bindings for global variables
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C).
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    let cmp_global_ctxt_helper (c:Ctxt.t) (p:Ast.decl) =
      match p with
        | Ast.Gvdecl { elt=gd } ->
          let ty =
            begin match gd.init.elt with
              | CNull t -> cmp_ty (Ast.TRef t)
              | CBool _ -> I1
              | CInt _ -> I64
              | CStr _ -> Ptr (cmp_rty Ast.RString)
              | CArr(t,_) -> Ptr (cmp_rty (Ast.RArray t))
              | _ -> failwith "not implemented yet"
            end
          in
          let pty = Ptr ty in
          Ctxt.add c gd.name (pty, Gid gd.name)
        | _ -> c
    in
    List.fold_left cmp_global_ctxt_helper c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   3. Compile the body of the function using cmp_block
   4. Use cfg_of_stream to produce a LLVMlite cfg from
 *)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  (*args and return type*)
  let rt_ty_ll = (cmp_ret_ty f.elt.frtyp) in
  let f_types = (List.map (fun( ty,id ) -> cmp_ty ty) f.elt.args) in
  let params = List.map (fun( ty,id ) -> id) f.elt.args in

  (*Setup new context by adding in local variables and the function itself TODO: Verify if this is right*)
  let arg_ctxt, arg_stream = 
    (List.fold_left 
      (fun (acc_c, acc_stream: Ctxt.t * stream) (ty,id) -> 
        let new_arg_op = gensym id in
        (Ctxt.add acc_c id (Ptr((cmp_ty ty)), Id new_arg_op )), 
        acc_stream >@ 
          [E (new_arg_op, Alloca (cmp_ty ty));
           I (new_arg_op, Store((cmp_ty ty), Id id, Id new_arg_op))
          ] 
      ) 
      (c,[])
      f.elt.args) 
  in
  let arg_fun_ctxt = (Ctxt.add arg_ctxt f.elt.fname (Ptr (Fun (f_types, rt_ty_ll)), Gid f.elt.fname) ) in

  let ins_stream = arg_stream >@ (cmp_block arg_fun_ctxt rt_ty_ll f.elt.body) in
  let f_cfg = cfg_of_stream ins_stream in
  match f_cfg with cfg, gdecl_list -> 
    { f_ty = (f_types , rt_ty_ll); f_param = params; f_cfg = cfg}, gdecl_list


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations
*)
let rec cmp_gexp (c:Ctxt.t) (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull t -> (cmp_ty (Ast.TRef t), GNull), []
  | CStr s ->
    let gid = gensym "str" in
    let ll_ty = str_arr_ty s in
    let cast = GBitcast (Ptr ll_ty, GGid gid, Ptr I8) in
    (Ptr I8, cast), [gid, (ll_ty, GString s)]

  | CBool true -> (I1, GInt 1L), []
  | CBool false -> (I1, GInt 0L), []
  | CInt i -> (I64, GInt i), []
  | CArr (ty, elements ) -> 
    let gid = gensym "g_array" in
    let length = (List.length elements) in 

    let oat_arr_ty = (cmp_rty (Ast.RArray ty)) in
    let ll_ty = Struct [I64; Array(length, (cmp_ty ty))] in

    let cast = GBitcast (Ptr ll_ty, GGid gid, Ptr oat_arr_ty) in
    let ginits ,gdecls = List.fold_left 
    (fun (acc_init, acc_decl : Ll.gdecl list * (Ll.gid * Ll.gdecl) list) (elt : Ast.exp node) ->
      let ginit, gdecls = cmp_gexp c elt in
      acc_init @ [ginit], acc_decl @ gdecls
    )
    ([],[])
    elements
    in 
    (Ptr oat_arr_ty, cast), gdecls @ [gid, (ll_ty, GStruct [(I64, GInt(Int64.of_int length)); (Array(length, (cmp_ty ty)) ,GArray ginits) ])]

  | _ -> failwith "cmp_gexp not implemented"


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } ->
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
