{
  open A3
  exception Not_implemented
}

(*
  Below is a dummy implementation. Please note the following
  - Tokens are defined in A3.mly
  - Return type is token and not token list
  - End of buffer is indicated by EOF token below
  - There is no trailer. The scanner function is written in the wrapper file (test_a4.ml)
  - This is sample implementation. Please rewrite them as per the specifications
*)

let plus =  '+'
let minus = '-'
let mult =  '*'
let unaryminus = '~'
let abs =   "abs"
let div =   "div"
let mod =   "mod"

let open_paren = '('
let closing_paren = ')'


let bool_true = 'T'
let bool_false = 'F'
let bool_not = "not"
let bool_and = "/\\"
let bool_or = "\\/"

let eq = '='
let gt = '>'
let lt = '<'

let if_cond = "if"
let then_cond = "then"
let else_cond = "else"
let fi_cond = "fi"

let identifier = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'' ]*
let whitespace = [' ' '\t' '\n' '\r']+
let comma = ','
let proj = "proj"


let digits = ['0'-'9']
let nonzeroDigits = ['1'-'9']
let integers =  ('0'|(nonzeroDigits digits*))


let defStr = "def"
let localStr = "local"
let inStr = "in"
let semicolon = ';'
let parallel = "||"
let endStr = "end"
let dot ='.'
let backslash = '\\'

let colon = ":"
let letStr = "let"
let tint = "Tint"
let tbool = "Tbool"
let tunit = "Tunit"



rule read = parse
eof                { EOF }

    | colon            {COLON}
    | tint             {ITYPE}
    | tbool            {BTYPE}
    | tunit            {UTYPE}
    



    | integers as n  { INT (int_of_string n) }
    | plus              { PLUS }
    | minus             {MINUS}
    | mult              { TIMES }
    | div               {DIV}
    | mod               {REM}
    | bool_and          {CONJ}
    | bool_or           {DISJ}
    | eq                {EQ}
    | gt                {GT}
    | lt                {LT}
    | open_paren        {LP}
    | closing_paren     {RP}
    | if_cond           {IF}
    | then_cond         {THEN}
    | else_cond         {ELSE}
    | fi_cond           {FI}
    | comma             {COMMA}
    | proj              {PROJ}
    | bool_true        {BOOL(true)}
    | bool_false       {BOOL(false)}
    | identifier  as id       {ID(id)}
    | abs              {ABS}
    | unaryminus       {TILDA}
    | bool_not         {NOT}


    | letStr              {LET}
    | localStr             {LOCAL}
    | defStr             {DEF}
    | dot              {DOT}
    | inStr             {IN}
    | semicolon         {SEMICOLON}
    | parallel          {PARALLEL}
    | endStr            {END}
    | backslash         {BACKSLASH}
    | whitespace       {read lexbuf}


    | _                { raise Not_implemented }
