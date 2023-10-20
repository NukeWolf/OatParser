%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */

// type
%token TBOOL    /* boolean */

// bop
%token LTLT     /* << */
%token GTGT     /* >> */
%token GTGTGT   /* >>> */
%token LT       /* < */
%token LTEQ     /* <= */
%token GT       /* > */
%token GTEQ     /* >= */
%token BANGEQ   /* != */
%token AMP      /* & */
%token PIPE     /* | */
%token BAND /* [&] */
%token BOR /* [|] */

// gexp
%token TRUE     /* true */
%token FALSE    /* false */
%token NEW      /* new */

// stmt
%token FOR      /* for */

// these need to be in order as defined by precedence
%left BOR
%left BAND
%left PIPE
%left AMP
%left EQEQ BANGEQ
%left LT LTEQ GT GTEQ
%left LTLT GTGT GTGTGT

%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | r=rtyp { TRef r } 


%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq } 
  // %token LTLT     /* << */
  | LTLT    { Shl }
  // %token GTGT     /* >> */
  | GTGT    { Shr }
  // %token GTGTGT   /* >>> */
  | GTGTGT  { Sar }
  // %token LT       /* < */
  | LT      { Lt }
  // %token LTEQ     /* <= */
  | LTEQ    { Lte }
  // %token GT       /* > */
  | GT      { Gt }
  // %token GTEQ     /* >= */
  | GTEQ    { Gte }
  // %token BANGEQ   /* != */
  | BANGEQ  { Neq }
  // %token AMP      /* & */
  | AMP     { And }
  // %token PIPE     /* | */
  | PIPE    { Or }
  // %token BAND /* [&] */
  | BAND { IAnd }
  // %token BOR /* [|] */
  | BOR { IOr }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT      { loc $startpos $endpos @@ CInt i } 
  | s=STRING   { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL { loc $startpos $endpos @@ CNull t }
  | TRUE       { loc $startpos $endpos @@ CBool true }
  | FALSE      { loc $startpos $endpos @@ CBool false }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
               { loc $startpos $endpos @@ CArr (t, es) }


lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  // | integer 64-bit integer literals
  | i=INT               { loc $startpos $endpos @@ CInt i }
  // | string C-style strings
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  // | ref null
  | t=rtyp NULL           { loc $startpos $endpos @@ CNull t }
  // | true
  | TRUE                { loc $startpos $endpos @@ CBool true }
  // | false
  | FALSE               { loc $startpos $endpos @@ CBool false }
  // | new t[]{exp1, .. ,expn} Explicitly initialized array
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }
  // | new int [exp1] Default-initialize int array
  // | new bool [exp1] Default-initialize bool array
  // note: i'm not sure how to restrict to only int and bool arrays
  | NEW t=ty LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr (t, e) }
  // | exp1 bop exp2
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  // | uop exp
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  // | id
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  // | exp1[exp2]
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  // | id(exp1, .. ,expn)
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }
  // | (exp)
  | LPAREN e=exp RPAREN { e } 

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

// these 3 grammar objects are for for loops
vdecls:
  | vdecls=separated_list(COMMA, vdecl) { vdecls }

expopt:
  | (* empty *) { None }
  | e=exp { Some e }

stmtopt:
  | (* empty *) { None }
  | s=stmt { Some s }

stmt: 
  // | vdecl;
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  // | lhs = exp;
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  // | id(exp1, .. ,expn);
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  // | if _stmt
  | ifs=if_stmt         { ifs }
  // | return ;
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  // | return exp;
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  // | while(exp) block
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 
  // | for(vdecls; expopt; stmtopt) block
  | FOR LPAREN v=vdecls SEMI e=expopt SEMI s=stmtopt RPAREN b=block
                        { loc $startpos $endpos @@ For(v, e, s, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
