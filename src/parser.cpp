// A Bison parser, made by GNU Bison 3.0.4.

// Skeleton implementation for Bison GLR parsers in C

// Copyright (C) 2002-2015 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.

/* C GLR parser skeleton written by Paul Hilfinger.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "glr.cc"

/* Pure parsers.  */
#define YYPURE 1






/* First part of user declarations.  */
#line 1 "src/syntax.y" // glr.c:240

#ifndef AN_PARSER
#define AN_PARSER

#include <stdlib.h>
#include <stdio.h>
#include <tokens.h>
#include <ptree.h>

#ifndef YYSTYPE
#define YYSTYPE Node*
#endif

/* This has no effect when generating a c++ parser */
/* Setting verbose for a c++ parser requires %error-verbose, set in the next section */
#define YYERROR_VERBOSE

#include "yyparser.h"

/* Defined in lexer.cpp */
extern int yylex(...);

namespace ante{
    extern void error(string& msg, const char *fileName, unsigned int row, unsigned int col);
}

void yyerror(const char *msg);


#line 84 "src/parser.cpp" // glr.c:240

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "yyparser.h"

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* Default (constant) value used for initialization for null
   right-hand sides.  Unlike the standard yacc.c template, here we set
   the default value of $$ to a zeroed-out value.  Since the default
   value is undefined, this behavior is technically correct.  */
static YYSTYPE yyval_default;

/* Copy the second part of user declarations.  */
#line 111 "src/parser.cpp" // glr.c:263
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (/*CONSTCOND*/ false)
# endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].yystate.yyloc)
static void yyerror (yy::parser& yyparser, const char* msg);
#line 133 "src/parser.cpp" // glr.c:263

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YYFREE
# define YYFREE free
#endif
#ifndef YYMALLOC
# define YYMALLOC malloc
#endif
#ifndef YYREALLOC
# define YYREALLOC realloc
#endif

#define YYSIZEMAX ((size_t) -1)

#ifdef __cplusplus
   typedef bool yybool;
#else
   typedef unsigned char yybool;
#endif
#define yytrue 1
#define yyfalse 0

#ifndef YYSETJMP
# include <setjmp.h>
# define YYJMP_BUF jmp_buf
# define YYSETJMP(Env) setjmp (Env)
/* Pacify clang.  */
# define YYLONGJMP(Env, Val) (longjmp (Env, Val), YYASSERT (0))
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#ifndef YYASSERT
# define YYASSERT(Condition) ((void) ((Condition) || (abort (), 0)))
#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  4
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1441

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  91
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  58
/* YYNRULES -- Number of rules.  */
#define YYNRULES  203
/* YYNRULES -- Number of states.  */
#define YYNSTATES  398
/* YYMAXRHS -- Maximum number of symbols on right-hand side of rule.  */
#define YYMAXRHS 9
/* YYMAXLEFT -- Maximum number of symbols to the left of a handle
   accessed by $0, $-1, etc., in any rule.  */
#define YYMAXLEFT 0

/* YYTRANSLATE(X) -- Bison symbol number corresponding to X.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   324

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,    77,    89,    84,
      81,    80,    75,    73,    70,    74,    79,    76,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    88,    69,
      71,    87,    72,     2,    90,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    82,     2,    85,    78,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    86,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    83
};

#if YYDEBUG
/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned short int yyrline[] =
{
       0,   115,   115,   118,   119,   120,   121,   124,   125,   132,
     133,   134,   135,   136,   137,   138,   142,   143,   144,   145,
     146,   149,   152,   155,   158,   161,   164,   165,   166,   167,
     168,   169,   170,   171,   172,   173,   174,   175,   176,   177,
     178,   179,   180,   181,   182,   187,   188,   189,   190,   191,
     192,   195,   196,   197,   200,   209,   210,   211,   212,   213,
     214,   215,   216,   219,   220,   223,   227,   228,   229,   230,
     233,   234,   235,   236,   240,   241,   242,   243,   244,   247,
     248,   251,   254,   255,   256,   257,   260,   261,   262,   265,
     266,   269,   273,   274,   275,   276,   279,   282,   283,   284,
     285,   288,   289,   290,   291,   294,   295,   298,   305,   306,
     309,   310,   313,   314,   315,   316,   317,   320,   323,   326,
     327,   330,   331,   332,   333,   336,   339,   342,   345,   348,
     351,   352,   353,   354,   357,   358,   359,   360,   361,   362,
     363,   364,   365,   366,   367,   368,   371,   372,   375,   376,
     379,   380,   383,   386,   387,   392,   393,   394,   395,   398,
     401,   402,   403,   404,   405,   406,   407,   408,   409,   410,
     411,   412,   413,   414,   415,   416,   417,   418,   419,   420,
     421,   426,   429,   430,   433,   434,   435,   436,   437,   438,
     439,   440,   441,   442,   443,   444,   445,   446,   447,   448,
     449,   450,   451,   452
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "Ident", "UserType", "I8", "I16", "I32",
  "I64", "U8", "U16", "U32", "U64", "Isz", "Usz", "F16", "F32", "F64",
  "C8", "C32", "Bool", "Void", "Eq", "NotEq", "AddEq", "SubEq", "MulEq",
  "DivEq", "GrtrEq", "LesrEq", "Or", "And", "Range", "True", "False",
  "IntLit", "FltLit", "StrLit", "Return", "If", "Elif", "Else", "For",
  "While", "Do", "In", "Continue", "Break", "Import", "Let", "Match",
  "Data", "Enum", "Pub", "Pri", "Pro", "Raw", "Const", "Ext", "Noinit",
  "Pathogen", "Where", "Infect", "Cleanse", "Ct", "Newline", "Indent",
  "Unindent", "LOW", "';'", "','", "'<'", "'>'", "'+'", "'-'", "'*'",
  "'/'", "'%'", "'^'", "'.'", "')'", "'('", "'['", "HIGH", "'\\''", "']'",
  "'|'", "'='", "':'", "'&'", "'@'", "$accept", "top_level_stmt_list",
  "stmt_list", "maybe_newline", "no_nl_stmt", "nl_stmt", "ident",
  "usertype", "intlit", "fltlit", "strlit", "lit_type", "type",
  "type_expr_", "type_expr", "modifier", "modifier_list_", "modifier_list",
  "var_decl", "let_binding", "var_assign", "usertype_list", "generic",
  "data_decl", "type_decl", "type_decl_list", "type_decl_block",
  "val_init_list", "enum_block", "enum_decl", "block", "raw_ident_list",
  "ident_list", "params", "maybe_params", "fn_decl", "fn_call", "ret_stmt",
  "elif_list", "maybe_elif_list", "if_stmt", "while_loop", "do_while_loop",
  "for_loop", "var", "ref_val", "val", "tuple", "array", "maybe_expr",
  "expr_list", "expr_list_p", "unary_op", "expr", "binop", "nl_expr",
  "nl_expr_list", "expr_block_p", YY_NULLPTR
};
#endif

#define YYPACT_NINF -171
#define YYTABLE_NINF -1

  // YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
  // STATE-NUM.
static const short int yypact[] =
{
     -19,  -171,    40,   495,  -171,  -171,  -171,  -171,  -171,  -171,
    -171,  -171,  -171,  -171,  -171,  -171,  -171,  -171,  -171,  -171,
    -171,  -171,  -171,  -171,   729,   729,    48,   729,    34,  1028,
      99,     7,  -171,  -171,  -171,  -171,  -171,  -171,  -171,  -171,
    1191,    48,    19,    19,   397,  -171,     3,   -58,  -171,  -171,
     -12,   -52,    48,  -171,   301,  1142,  -171,  -171,  -171,  -171,
    -171,  -171,  -171,  -171,  -171,  -171,  -171,  -171,    23,  -171,
    -171,  -171,  -171,  -171,    48,   817,   940,   553,   641,   940,
     940,    30,  -171,  -171,  -171,   940,  -171,  -171,  -171,  -171,
    -171,  -171,  -171,  1205,    62,    69,    62,   729,   -59,    48,
    1047,   -46,    99,    70,  -171,    55,  -171,    66,  -171,  -171,
    -171,  -171,    87,  -171,   553,   729,  -171,  -171,  1166,    71,
    1191,  1191,   -16,  -171,    99,     7,    48,   729,   729,   729,
     729,   729,    75,    48,  -171,   102,   101,  1266,  -171,  -171,
     905,    93,   104,    97,  -171,    95,  -171,  -171,  -171,  -171,
     729,   729,   729,   729,   729,   729,   729,    48,   -19,   729,
     729,   729,   729,   729,   729,   729,   729,    48,   729,   495,
      50,   729,  -171,    62,   729,  1191,   103,   105,    48,  1085,
      99,   115,  -171,   107,    11,  -171,  -171,  -171,   106,  -171,
     108,  -171,    12,    14,   729,   729,  1191,   -46,    70,  -171,
      25,  -171,  -171,  -171,  -171,  -171,   729,   127,  -171,   -19,
     -19,   -19,   -19,   -19,   -19,   -19,    48,   -19,   -19,   -19,
     -19,   -19,   -19,   -19,   -19,   -19,   -19,   817,  -171,   729,
    -171,  -171,     6,     6,     6,     6,  1048,   447,    64,   128,
     729,     6,     6,   -18,   -18,    20,    20,    20,    20,  -171,
    -171,   153,   495,   119,    82,   729,    62,    84,  -171,    62,
    -171,  -171,    48,   112,   154,   729,   729,   156,    48,   137,
    -171,    94,  -171,  -171,    83,  -171,   729,    99,  -171,  -171,
    -171,   165,  -171,  -171,    62,   115,  -171,  -171,   729,   729,
    1191,   201,   817,   817,   817,   817,   817,   817,   817,   817,
     160,   817,   817,   817,   817,   817,   817,   817,   817,   817,
     817,   786,  -171,   729,  1301,  -171,   181,   100,  -171,  -171,
      62,  -171,   729,    62,  -171,  -171,    48,  -171,  1191,   729,
    -171,  -171,   729,  -171,  1085,  -171,    99,  -171,  -171,   163,
     164,  -171,  -171,   176,  -171,    62,   729,  1240,  1266,   218,
     218,   218,   218,  1336,  1359,   -19,  1324,   218,   218,   197,
     197,    44,    44,    44,    44,   175,   -19,  1301,  -171,  -171,
    -171,    62,  -171,  -171,    48,  -171,  -171,  -171,  -171,   729,
    1191,   170,  -171,  1301,   -19,   817,  -171,  -171,  -171,  -171,
      62,  1191,   817,  1324,  -171,    62,  1324,  -171
};

  // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
  // Performed when YYTABLE does not specify something else to do.  Zero
  // means the default is an error.
static const unsigned char yydefact[] =
{
       8,     7,     0,     0,     1,    21,    22,    26,    27,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,     0,     0,     0,     0,     0,     0,
       0,     0,    55,    56,    57,    58,    59,    60,    61,    62,
       0,     0,     0,     0,     8,     6,     0,   133,    43,    50,
      53,    54,     0,    64,    65,     0,    16,    20,    17,    10,
      11,     9,    18,    19,    15,    12,    13,    14,     0,   144,
     145,    23,    24,    25,     0,     0,     0,     0,     0,     0,
       0,   129,   141,   142,   143,     0,   134,   140,   180,   136,
     137,   139,   118,   159,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   100,     0,    44,   133,   130,   131,
       2,     4,     0,     5,     0,     0,   117,    45,     0,     0,
       0,     0,    69,    63,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   203,     0,   181,   183,   157,   147,
       0,     0,   152,   154,   149,     0,   154,   156,   155,   158,
       0,     0,     0,     0,     0,     0,     0,     0,     8,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     124,     0,   126,     0,     0,   111,     0,     0,     0,     0,
       0,     0,    84,    95,     0,    98,    49,     3,     0,    48,
       0,    46,    51,    52,   151,     0,   111,     0,     0,    99,
      67,    75,    76,    77,    78,    74,     0,     0,   138,     8,
       8,     8,     8,     8,     8,     8,     0,     8,     8,     8,
       8,     8,     8,     8,     8,     8,     8,     0,   146,     0,
     135,   148,   173,   174,   175,   176,   177,   178,   179,     0,
       0,   165,   166,   160,   161,   162,   163,   164,   167,   129,
     168,     0,     0,     6,     0,     0,     0,   122,   125,     0,
     127,    73,     0,   110,     0,     0,     0,     0,    87,     0,
      90,     0,    88,    80,     0,    85,     0,     0,    96,   132,
      47,     0,   150,    68,     0,     0,    82,    97,   151,     0,
     111,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   153,     0,   169,   170,     4,     0,   103,   104,
       0,   123,     0,     0,   128,   106,   107,   109,     0,     0,
      72,    71,     0,    86,     0,    91,     0,    81,    94,    92,
       0,   114,    83,     0,    66,     0,     0,     0,   182,   197,
     198,   199,   200,   201,   202,     8,   193,   189,   190,   184,
     185,   186,   187,   188,   191,   192,     8,   171,   101,   102,
     120,     0,   121,   105,     0,   116,    70,    89,    79,     0,
     111,     0,   112,   172,     8,     0,   194,   119,   108,    93,
       0,   111,     0,   195,   115,     0,   196,   113
};

  // YYPGOTO[NTERM-NUM].
static const short int yypgoto[] =
{
    -171,  -171,    90,   -13,   -36,   -25,     1,     5,  -171,  -171,
    -171,  -171,   -66,  -171,    -3,   206,  -171,   -28,  -171,  -171,
    -171,  -171,    65,  -171,   -68,  -171,  -164,  -171,   -93,  -170,
     -81,  -171,  -113,  -171,  -140,  -171,    18,  -171,  -171,  -171,
    -171,  -171,  -171,  -171,   113,    89,   -73,   -42,  -171,   -21,
     190,  -171,  -171,   -11,   184,  -171,  -171,    88
};

  // YYDEFGOTO[NTERM-NUM].
static const short int yydefgoto[] =
{
      -1,     2,    44,     3,    45,    46,    81,    48,    82,    83,
      84,    49,    50,    51,    85,    53,    54,    55,    56,    57,
      58,   274,   181,    59,   270,   271,   182,   184,   104,    60,
     170,   326,   327,   263,   264,    61,    86,    63,   257,   258,
      64,    65,    66,    67,    87,    68,    88,    89,    90,   281,
     141,   142,    91,   146,    93,   135,   136,   137
};

  // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
  // positive, shift that token.  If negative, reduce the rule whose
  // number is the opposite.  If YYTABLE_NINF, syntax error.
static const unsigned short int yytable[] =
{
      52,   100,   134,   138,    47,   116,   147,   148,   111,   272,
     185,     6,   149,    92,    94,   172,    96,   275,   120,   112,
     179,    62,     5,   114,   115,   180,    99,    95,   174,   175,
      98,   110,   199,   286,   121,   101,   103,   105,   156,   116,
       4,    52,   106,   107,   107,    47,     1,   127,   128,   129,
     130,     5,   126,   122,   192,   193,   284,   163,   164,   165,
     166,   167,    62,   117,   168,   194,   143,   149,   113,   118,
     119,   195,   196,   102,   140,   132,   277,    97,   278,   161,
     162,   163,   164,   165,   166,   167,   173,   117,   168,   117,
     255,   256,   260,   118,   119,   118,   119,   178,   166,   167,
     176,   177,   168,     6,   188,   287,   288,   183,    42,    43,
     131,   114,   289,   290,   171,   190,   201,   202,   203,   204,
     205,   342,   225,   226,   322,   323,   227,   200,   169,   197,
     198,   108,   109,   253,   207,   186,   102,   161,   162,   163,
     164,   165,   166,   167,   254,   240,   168,   113,   115,   319,
     345,   269,   187,   336,   134,   337,   191,   251,   239,   334,
     259,   335,   206,   261,   272,   187,    52,   369,   249,   208,
      47,   209,   262,   228,   229,   321,   268,   230,   324,   267,
     231,   179,   328,   282,   283,   273,   318,    62,   280,   125,
     265,   279,   266,   262,   276,   291,   293,   294,   295,   296,
     297,   298,   299,   341,   301,   302,   303,   304,   305,   306,
     307,   308,   309,   310,   292,   313,   316,   300,   312,   134,
     134,   134,   134,   134,   134,   134,   134,   317,   134,   134,
     134,   134,   134,   134,   134,   134,   134,   134,   315,   370,
     390,   329,   372,   332,   320,   340,   346,   355,   368,    52,
     379,   395,   380,    47,   330,   331,   381,   227,   391,   252,
     123,   388,   285,   325,   382,   338,   377,   343,   145,   333,
      62,     0,   222,   223,   224,   225,   226,   282,   344,   227,
     250,     0,   339,     0,     0,     0,     0,   262,     0,     0,
     387,   220,   221,   222,   223,   224,   225,   226,     0,     0,
     227,     0,     0,     0,     0,     0,   269,     0,     0,   394,
       0,   371,   134,     0,   397,   311,     0,     0,   375,   134,
       0,   376,     0,     0,     0,   374,     0,   373,     0,     0,
       0,   268,     0,     0,   232,   233,   234,   235,   236,   237,
     238,   378,   385,   241,   242,   243,   244,   245,   246,   247,
     248,     0,     0,   386,    32,    33,    34,    35,    36,    37,
      38,    39,     0,     0,     0,     0,     0,     0,   389,     0,
       0,   392,     0,     0,     0,   325,     0,   262,     0,     0,
     347,   348,   349,   350,   351,   352,   353,   354,   262,   356,
     357,   358,   359,   360,   361,   362,   363,   364,   365,     0,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,     0,
       0,     0,     0,     0,   314,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    24,    25,     0,     0,    26,
      27,    28,     0,     0,     0,     0,    29,     0,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,     0,     0,
       0,     0,     1,     0,     0,     0,     0,     0,     0,   150,
     151,     0,     0,   393,     0,   152,   153,     0,    40,   156,
     396,    41,     0,     0,     0,     0,    42,    43,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   367,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,     0,   159,   160,
     161,   162,   163,   164,   165,   166,   167,     0,     0,   168,
     383,     0,     0,    24,    25,     0,     0,    26,    27,    28,
       0,     0,     0,     0,    29,     0,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,     0,    40,     0,     0,    41,
       0,     0,     0,     0,    42,    43,    69,    70,    71,    72,
      73,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    74,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    75,
       0,     0,     0,     0,     0,     0,     0,    76,     0,     0,
       0,     0,     0,   139,    77,    78,     0,    41,     0,     0,
       0,     0,    79,    80,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    69,    70,    71,    72,    73,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      74,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    75,     0,     0,
       0,     0,     0,     0,     0,    76,     0,     0,     0,     0,
       0,     0,    77,    78,     0,    41,   144,     0,     0,     0,
      79,    80,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    69,    70,    71,    72,    73,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    74,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    75,     0,     0,     0,     0,
       0,     0,     0,    76,     0,     0,     0,     0,   210,   211,
      77,    78,     0,    41,   212,   213,   214,   215,    79,    80,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,     0,
       0,     0,     0,     0,     0,     0,     0,   216,     0,     0,
      69,    70,    71,    72,    73,   217,     0,   218,   219,   220,
     221,   222,   223,   224,   225,   226,   133,     0,   227,     0,
       0,   366,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    75,     0,     0,     0,     0,     0,     0,
       0,    76,     0,     0,     0,     0,     0,     0,    77,    78,
       0,    41,     0,     0,     0,     0,    79,    80,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    69,    70,
      71,    72,    73,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    75,     0,    69,    70,    71,    72,    73,     0,    76,
       0,     0,     0,     0,     0,   186,    77,    78,     0,    41,
       0,     0,     0,     0,    79,    80,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    75,     0,     0,     0,
       0,     0,     0,     0,    76,     0,     0,     0,     0,     0,
       0,    77,    78,     0,    41,     0,     0,     0,     0,    79,
      80,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,     0,
     150,   151,     0,     0,     0,     0,   152,   153,     0,   155,
     156,    32,    33,    34,    35,    36,    37,    38,    39,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,     0,     0,    40,
       0,     0,    41,     0,     0,     0,     0,     0,     0,   159,
     160,   161,   162,   163,   164,   165,   166,   167,    40,     0,
     168,    41,     0,     0,     0,     0,     0,    31,    32,    33,
      34,    35,    36,    37,    38,    39,     6,     7,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,     0,     0,    40,     0,     0,    41,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,     0,     0,
       0,     0,     0,   124,   125,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    40,     0,     0,    41,   150,   151,     0,
       0,     0,     0,   152,   153,   154,   155,   156,     0,     0,
       0,     0,     0,     0,     0,     0,   189,    40,     0,     0,
      41,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   210,   211,     0,     0,   157,     0,   212,   213,
     214,   215,    40,     0,   158,    41,   159,   160,   161,   162,
     163,   164,   165,   166,   167,   384,     0,   168,   210,   211,
       0,     0,     0,     0,   212,   213,   214,   215,     0,     0,
       0,   216,     0,     0,     0,     0,     0,     0,     0,   217,
       0,   218,   219,   220,   221,   222,   223,   224,   225,   226,
       0,     0,   227,   150,   151,     0,     0,   216,     0,   152,
     153,   154,   155,   156,     0,   217,     0,   218,   219,   220,
     221,   222,   223,   224,   225,   226,   210,   211,   227,     0,
       0,     0,   212,   213,   214,   215,     0,     0,   210,   211,
       0,     0,   157,     0,   212,   213,     0,   215,     0,     0,
       0,     0,   159,   160,   161,   162,   163,   164,   165,   166,
     167,   210,   211,   168,     0,   216,     0,   212,   213,     0,
       0,     0,     0,     0,     0,   218,   219,   220,   221,   222,
     223,   224,   225,   226,     0,     0,   227,   218,   219,   220,
     221,   222,   223,   224,   225,   226,     0,     0,   227,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     218,   219,   220,   221,   222,   223,   224,   225,   226,     0,
       0,   227
};

static const short int yycheck[] =
{
       3,    29,    75,    76,     3,    47,    79,    80,    44,   179,
     103,     4,    85,    24,    25,    96,    27,   181,    70,    44,
      66,     3,     3,    81,    82,    71,    29,    26,    87,    88,
      29,    44,   125,   197,    86,    30,    31,    40,    32,    81,
       0,    44,    41,    42,    43,    44,    65,    24,    25,    26,
      27,     3,    55,    52,   120,   121,   196,    75,    76,    77,
      78,    79,    44,    75,    82,    81,    77,   140,    65,    81,
      82,    87,    88,    66,    77,    74,    65,    43,    67,    73,
      74,    75,    76,    77,    78,    79,    97,    75,    82,    75,
      40,    41,   173,    81,    82,    81,    82,   100,    78,    79,
      99,   100,    82,     4,   115,   198,    81,   102,    89,    90,
      87,    81,    87,    88,    45,   118,   127,   128,   129,   130,
     131,   285,    78,    79,    40,    41,    82,   126,    66,   124,
     125,    42,    43,   169,   133,    80,    66,    73,    74,    75,
      76,    77,    78,    79,   169,   158,    82,    65,    82,    67,
     290,   179,    65,    70,   227,    72,    85,   168,   157,    65,
     171,    67,    87,   174,   334,    65,   169,    67,   167,    67,
     169,    70,   175,    80,    70,   256,   179,    80,   259,   178,
      85,    66,    70,   194,   195,   180,    67,   169,    80,    52,
      87,    85,    87,   196,    87,   206,   209,   210,   211,   212,
     213,   214,   215,   284,   217,   218,   219,   220,   221,   222,
     223,   224,   225,   226,    87,    87,   252,   216,   229,   292,
     293,   294,   295,   296,   297,   298,   299,   252,   301,   302,
     303,   304,   305,   306,   307,   308,   309,   310,    85,   320,
     380,    87,   323,    87,   255,    80,    45,    87,    67,   252,
      87,   391,    88,   252,   265,   266,    80,    82,    88,   169,
      54,   374,   197,   262,   345,   276,   334,   288,    78,   268,
     252,    -1,    75,    76,    77,    78,    79,   288,   289,    82,
     167,    -1,   277,    -1,    -1,    -1,    -1,   290,    -1,    -1,
     371,    73,    74,    75,    76,    77,    78,    79,    -1,    -1,
      82,    -1,    -1,    -1,    -1,    -1,   334,    -1,    -1,   390,
      -1,   322,   385,    -1,   395,   227,    -1,    -1,   329,   392,
      -1,   332,    -1,    -1,    -1,   328,    -1,   326,    -1,    -1,
      -1,   334,    -1,    -1,   150,   151,   152,   153,   154,   155,
     156,   336,   355,   159,   160,   161,   162,   163,   164,   165,
     166,    -1,    -1,   366,    53,    54,    55,    56,    57,    58,
      59,    60,    -1,    -1,    -1,    -1,    -1,    -1,   379,    -1,
      -1,   384,    -1,    -1,    -1,   374,    -1,   380,    -1,    -1,
     292,   293,   294,   295,   296,   297,   298,   299,   391,   301,
     302,   303,   304,   305,   306,   307,   308,   309,   310,    -1,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,   240,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    38,    39,    -1,    -1,    42,
      43,    44,    -1,    -1,    -1,    -1,    49,    -1,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    -1,    -1,
      -1,    -1,    65,    -1,    -1,    -1,    -1,    -1,    -1,    22,
      23,    -1,    -1,   385,    -1,    28,    29,    -1,    81,    32,
     392,    84,    -1,    -1,    -1,    -1,    89,    90,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   313,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    -1,    -1,    82,
     346,    -1,    -1,    38,    39,    -1,    -1,    42,    43,    44,
      -1,    -1,    -1,    -1,    49,    -1,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    -1,    81,    -1,    -1,    84,
      -1,    -1,    -1,    -1,    89,    90,    33,    34,    35,    36,
      37,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    49,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    66,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    -1,    -1,
      -1,    -1,    -1,    80,    81,    82,    -1,    84,    -1,    -1,
      -1,    -1,    89,    90,     3,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    33,    34,    35,    36,    37,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      49,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    -1,    -1,    -1,    -1,
      -1,    -1,    81,    82,    -1,    84,    85,    -1,    -1,    -1,
      89,    90,     3,     4,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    33,    34,    35,    36,    37,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    49,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    -1,    -1,    -1,    -1,    22,    23,
      81,    82,    -1,    84,    28,    29,    30,    31,    89,    90,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,
      33,    34,    35,    36,    37,    69,    -1,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    49,    -1,    82,    -1,
      -1,    85,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    66,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    -1,    -1,    -1,    -1,    -1,    -1,    81,    82,
      -1,    84,    -1,    -1,    -1,    -1,    89,    90,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    33,    34,
      35,    36,    37,     3,     4,     5,     6,     7,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    66,    -1,    33,    34,    35,    36,    37,    -1,    74,
      -1,    -1,    -1,    -1,    -1,    80,    81,    82,    -1,    84,
      -1,    -1,    -1,    -1,    89,    90,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    -1,    -1,    -1,    -1,    -1,
      -1,    81,    82,    -1,    84,    -1,    -1,    -1,    -1,    89,
      90,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    -1,
      22,    23,    -1,    -1,    -1,    -1,    28,    29,    -1,    31,
      32,    53,    54,    55,    56,    57,    58,    59,    60,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    -1,    81,
      -1,    -1,    84,    -1,    -1,    -1,    -1,    -1,    -1,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    81,    -1,
      82,    84,    -1,    -1,    -1,    -1,    -1,    52,    53,    54,
      55,    56,    57,    58,    59,    60,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    -1,    -1,    81,    -1,    -1,    84,
       4,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    -1,    -1,
      -1,    -1,    -1,    51,    52,     4,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    81,    -1,    -1,    84,    22,    23,    -1,
      -1,    -1,    -1,    28,    29,    30,    31,    32,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    80,    81,    -1,    -1,
      84,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    22,    23,    -1,    -1,    61,    -1,    28,    29,
      30,    31,    81,    -1,    69,    84,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    45,    -1,    82,    22,    23,
      -1,    -1,    -1,    -1,    28,    29,    30,    31,    -1,    -1,
      -1,    61,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    69,
      -1,    71,    72,    73,    74,    75,    76,    77,    78,    79,
      -1,    -1,    82,    22,    23,    -1,    -1,    61,    -1,    28,
      29,    30,    31,    32,    -1,    69,    -1,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    22,    23,    82,    -1,
      -1,    -1,    28,    29,    30,    31,    -1,    -1,    22,    23,
      -1,    -1,    61,    -1,    28,    29,    -1,    31,    -1,    -1,
      -1,    -1,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    22,    23,    82,    -1,    61,    -1,    28,    29,    -1,
      -1,    -1,    -1,    -1,    -1,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    -1,    -1,    82,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    -1,    -1,    82,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    -1,
      -1,    82
};

  // YYSTOS[STATE-NUM] -- The (internal number of the) accessing
  // symbol of state STATE-NUM.
static const unsigned char yystos[] =
{
       0,    65,    92,    94,     0,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    38,    39,    42,    43,    44,    49,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      81,    84,    89,    90,    93,    95,    96,    97,    98,   102,
     103,   104,   105,   106,   107,   108,   109,   110,   111,   114,
     120,   126,   127,   128,   131,   132,   133,   134,   136,    33,
      34,    35,    36,    37,    49,    66,    74,    81,    82,    89,
      90,    97,    99,   100,   101,   105,   127,   135,   137,   138,
     139,   143,   144,   145,   144,    97,   144,    43,    97,   105,
     108,    98,    66,    98,   119,   105,    97,    97,   136,   136,
      94,    95,    96,    65,    81,    82,   138,    75,    81,    82,
      70,    86,    97,   106,    51,    52,   105,    24,    25,    26,
      27,    87,    97,    49,   137,   146,   147,   148,   137,    80,
     105,   141,   142,   144,    85,   141,   144,   137,   137,   137,
      22,    23,    28,    29,    30,    31,    32,    61,    69,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    82,    66,
     121,    45,   121,   144,    87,    88,    97,    97,   105,    66,
      71,   113,   117,    98,   118,   119,    80,    65,   144,    80,
     105,    85,   103,   103,    81,    87,    88,    98,    98,   119,
      97,   144,   144,   144,   144,   144,    87,    97,    67,    70,
      22,    23,    28,    29,    30,    31,    61,    69,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    82,    80,    70,
      80,    85,   145,   145,   145,   145,   145,   145,   145,    97,
      94,   145,   145,   145,   145,   145,   145,   145,   145,    97,
     135,   144,    93,    95,    96,    40,    41,   129,   130,   144,
     121,   144,   105,   124,   125,    87,    87,    97,   105,   108,
     115,   116,   120,    98,   112,   117,    87,    65,    67,    85,
      80,   140,   144,   144,   125,   113,   117,   119,    81,    87,
      88,   144,    87,    94,    94,    94,    94,    94,    94,    94,
      97,    94,    94,    94,    94,    94,    94,    94,    94,    94,
      94,   148,   144,    87,   145,    85,    95,    96,    67,    67,
     144,   121,    40,    41,   121,    97,   122,   123,    70,    87,
     144,   144,    87,    97,    65,    67,    70,    72,   144,    98,
      80,   121,   117,   140,   144,   125,    45,   148,   148,   148,
     148,   148,   148,   148,   148,    87,   148,   148,   148,   148,
     148,   148,   148,   148,   148,   148,    85,   145,    67,    67,
     121,   144,   121,    97,   105,   144,   144,   115,    98,    87,
      88,    80,   121,   145,    45,    94,    94,   121,   123,   144,
     125,    88,    94,   148,   121,   125,   148,   121
};

  // YYR1[YYN] -- Symbol number of symbol that rule YYN derives.
static const unsigned char yyr1[] =
{
       0,    91,    92,    93,    93,    93,    93,    94,    94,    95,
      95,    95,    95,    95,    95,    95,    96,    96,    96,    96,
      96,    97,    98,    99,   100,   101,   102,   102,   102,   102,
     102,   102,   102,   102,   102,   102,   102,   102,   102,   102,
     102,   102,   102,   102,   102,   103,   103,   103,   103,   103,
     103,   104,   104,   104,   105,   106,   106,   106,   106,   106,
     106,   106,   106,   107,   107,   108,   109,   109,   109,   109,
     110,   110,   110,   110,   111,   111,   111,   111,   111,   112,
     112,   113,   114,   114,   114,   114,   115,   115,   115,   116,
     116,   117,   118,   118,   118,   118,   119,   120,   120,   120,
     120,   121,   121,   121,   121,   122,   122,   123,   124,   124,
     125,   125,   126,   126,   126,   126,   126,   127,   128,   129,
     129,   130,   130,   130,   130,   131,   132,   133,   134,   135,
     136,   136,   136,   136,   137,   137,   137,   137,   137,   137,
     137,   137,   137,   137,   137,   137,   138,   138,   139,   139,
     140,   140,   141,   142,   142,   143,   143,   143,   143,   144,
     145,   145,   145,   145,   145,   145,   145,   145,   145,   145,
     145,   145,   145,   145,   145,   145,   145,   145,   145,   145,
     145,   146,   147,   147,   148,   148,   148,   148,   148,   148,
     148,   148,   148,   148,   148,   148,   148,   148,   148,   148,
     148,   148,   148,   148
};

  // YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.
static const unsigned char yyr2[] =
{
       0,     2,     3,     3,     2,     2,     1,     1,     0,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     2,     2,     3,     4,     3,     3,
       1,     3,     3,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     2,     1,     1,     5,     3,     4,     2,
       6,     5,     5,     4,     3,     3,     3,     3,     3,     3,
       1,     3,     4,     5,     3,     4,     2,     1,     1,     3,
       1,     3,     3,     5,     3,     1,     3,     4,     3,     3,
       2,     4,     4,     3,     3,     2,     1,     1,     4,     2,
       1,     0,     6,     9,     5,     8,     6,     2,     2,     4,
       3,     3,     1,     2,     0,     4,     3,     4,     5,     1,
       2,     2,     4,     1,     1,     3,     1,     1,     3,     1,
       1,     1,     1,     1,     1,     1,     3,     2,     3,     2,
       1,     0,     1,     3,     1,     2,     2,     2,     2,     1,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     4,
       4,     5,     6,     3,     3,     3,     3,     3,     3,     3,
       1,     1,     4,     1,     4,     4,     4,     4,     4,     4,
       4,     4,     4,     4,     5,     6,     7,     4,     4,     4,
       4,     4,     4,     1
};


/* YYDPREC[RULE-NUM] -- Dynamic precedence of rule #RULE-NUM (0 if none).  */
static const unsigned char yydprec[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     2,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     1,     0,     0,     2,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0
};

/* YYMERGER[RULE-NUM] -- Index of merging function for rule #RULE-NUM.  */
static const unsigned char yymerger[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0
};

/* YYIMMEDIATE[RULE-NUM] -- True iff rule #RULE-NUM is not to be deferred, as
   in the case of predicates.  */
static const yybool yyimmediate[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0
};

/* YYCONFLP[YYPACT[STATE-NUM]] -- Pointer into YYCONFL of start of
   list of conflicting reductions corresponding to action entry for
   state STATE-NUM in yytable.  0 means no conflicts.  The list in
   yyconfl is terminated by a rule number of 0.  */
static const unsigned char yyconflp[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     1,
       3,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     5,     7,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0
};

/* YYCONFL[I] -- lists of conflicting rule numbers, each terminated by
   0, pointed into by YYCONFLP.  */
static const short int yyconfl[] =
{
       0,    53,     0,    53,     0,    52,     0,    52,     0
};

/* Error token number */
#define YYTERROR 1




#undef yynerrs
#define yynerrs (yystackp->yyerrcnt)
#undef yychar
#define yychar (yystackp->yyrawchar)
#undef yylval
#define yylval (yystackp->yyval)
#undef yylloc
#define yylloc (yystackp->yyloc)


static const int YYEOF = 0;
static const int YYEMPTY = -2;

typedef enum { yyok, yyaccept, yyabort, yyerr } YYRESULTTAG;

#define YYCHK(YYE)                              \
  do {                                          \
    YYRESULTTAG yychk_flag = YYE;               \
    if (yychk_flag != yyok)                     \
      return yychk_flag;                        \
  } while (0)

#if YYDEBUG

# ifndef YYFPRINTF
#  define YYFPRINTF fprintf
# endif

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YYDPRINTF(Args)                        \
  do {                                          \
    if (yydebug)                                \
      YYFPRINTF Args;                           \
  } while (0)


/*--------------------.
| Print this symbol.  |
`--------------------*/

static void
yy_symbol_print (FILE *, int yytype, const yy::parser::semantic_type *yyvaluep, yy::parser& yyparser)
{
  YYUSE (yyparser);
  yyparser.yy_symbol_print_ (yytype, yyvaluep);
}


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                  \
  do {                                                                  \
    if (yydebug)                                                        \
      {                                                                 \
        YYFPRINTF (stderr, "%s ", Title);                               \
        yy_symbol_print (stderr, Type, Value, yyparser);        \
        YYFPRINTF (stderr, "\n");                                       \
      }                                                                 \
  } while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;

struct yyGLRStack;
static void yypstack (struct yyGLRStack* yystackp, size_t yyk)
  YY_ATTRIBUTE_UNUSED;
static void yypdumpstack (struct yyGLRStack* yystackp)
  YY_ATTRIBUTE_UNUSED;

#else /* !YYDEBUG */

# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)

#endif /* !YYDEBUG */

/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYMAXDEPTH * sizeof (GLRStackItem)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif

/* Minimum number of free items on the stack allowed after an
   allocation.  This is to allow allocation and initialization
   to be completed by functions that call yyexpandGLRStack before the
   stack is expanded, thus insuring that all necessary pointers get
   properly redirected to new data.  */
#define YYHEADROOM 2

#ifndef YYSTACKEXPANDABLE
#  define YYSTACKEXPANDABLE 1
#endif

#if YYSTACKEXPANDABLE
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyexpandGLRStack (Yystack);                       \
  } while (0)
#else
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyMemoryExhausted (Yystack);                      \
  } while (0)
#endif


#if YYERROR_VERBOSE

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static size_t
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      size_t yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return strlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

#endif /* !YYERROR_VERBOSE */

/** State numbers, as in LALR(1) machine */
typedef int yyStateNum;

/** Rule numbers, as in LALR(1) machine */
typedef int yyRuleNum;

/** Grammar symbol */
typedef int yySymbol;

/** Item references, as in LALR(1) machine */
typedef short int yyItemNum;

typedef struct yyGLRState yyGLRState;
typedef struct yyGLRStateSet yyGLRStateSet;
typedef struct yySemanticOption yySemanticOption;
typedef union yyGLRStackItem yyGLRStackItem;
typedef struct yyGLRStack yyGLRStack;

struct yyGLRState {
  /** Type tag: always true.  */
  yybool yyisState;
  /** Type tag for yysemantics.  If true, yysval applies, otherwise
   *  yyfirstVal applies.  */
  yybool yyresolved;
  /** Number of corresponding LALR(1) machine state.  */
  yyStateNum yylrState;
  /** Preceding state in this stack */
  yyGLRState* yypred;
  /** Source position of the last token produced by my symbol */
  size_t yyposn;
  union {
    /** First in a chain of alternative reductions producing the
     *  non-terminal corresponding to this state, threaded through
     *  yynext.  */
    yySemanticOption* yyfirstVal;
    /** Semantic value for this state.  */
    YYSTYPE yysval;
  } yysemantics;
};

struct yyGLRStateSet {
  yyGLRState** yystates;
  /** During nondeterministic operation, yylookaheadNeeds tracks which
   *  stacks have actually needed the current lookahead.  During deterministic
   *  operation, yylookaheadNeeds[0] is not maintained since it would merely
   *  duplicate yychar != YYEMPTY.  */
  yybool* yylookaheadNeeds;
  size_t yysize, yycapacity;
};

struct yySemanticOption {
  /** Type tag: always false.  */
  yybool yyisState;
  /** Rule number for this reduction */
  yyRuleNum yyrule;
  /** The last RHS state in the list of states to be reduced.  */
  yyGLRState* yystate;
  /** The lookahead for this reduction.  */
  int yyrawchar;
  YYSTYPE yyval;
  /** Next sibling in chain of options.  To facilitate merging,
   *  options are chained in decreasing order by address.  */
  yySemanticOption* yynext;
};

/** Type of the items in the GLR stack.  The yyisState field
 *  indicates which item of the union is valid.  */
union yyGLRStackItem {
  yyGLRState yystate;
  yySemanticOption yyoption;
};

struct yyGLRStack {
  int yyerrState;


  int yyerrcnt;
  int yyrawchar;
  YYSTYPE yyval;

  YYJMP_BUF yyexception_buffer;
  yyGLRStackItem* yyitems;
  yyGLRStackItem* yynextFree;
  size_t yyspaceLeft;
  yyGLRState* yysplitPoint;
  yyGLRState* yylastDeleted;
  yyGLRStateSet yytops;
};

#if YYSTACKEXPANDABLE
static void yyexpandGLRStack (yyGLRStack* yystackp);
#endif

static _Noreturn void
yyFail (yyGLRStack* yystackp, yy::parser& yyparser, const char* yymsg)
{
  if (yymsg != YY_NULLPTR)
    yyerror (yyparser, yymsg);
  YYLONGJMP (yystackp->yyexception_buffer, 1);
}

static _Noreturn void
yyMemoryExhausted (yyGLRStack* yystackp)
{
  YYLONGJMP (yystackp->yyexception_buffer, 2);
}

#if YYDEBUG || YYERROR_VERBOSE
/** A printable representation of TOKEN.  */
static inline const char*
yytokenName (yySymbol yytoken)
{
  if (yytoken == YYEMPTY)
    return "";

  return yytname[yytoken];
}
#endif

/** Fill in YYVSP[YYLOW1 .. YYLOW0-1] from the chain of states starting
 *  at YYVSP[YYLOW0].yystate.yypred.  Leaves YYVSP[YYLOW1].yystate.yypred
 *  containing the pointer to the next state in the chain.  */
static void yyfillin (yyGLRStackItem *, int, int) YY_ATTRIBUTE_UNUSED;
static void
yyfillin (yyGLRStackItem *yyvsp, int yylow0, int yylow1)
{
  int i;
  yyGLRState *s = yyvsp[yylow0].yystate.yypred;
  for (i = yylow0-1; i >= yylow1; i -= 1)
    {
#if YYDEBUG
      yyvsp[i].yystate.yylrState = s->yylrState;
#endif
      yyvsp[i].yystate.yyresolved = s->yyresolved;
      if (s->yyresolved)
        yyvsp[i].yystate.yysemantics.yysval = s->yysemantics.yysval;
      else
        /* The effect of using yysval or yyloc (in an immediate rule) is
         * undefined.  */
        yyvsp[i].yystate.yysemantics.yyfirstVal = YY_NULLPTR;
      s = yyvsp[i].yystate.yypred = s->yypred;
    }
}

/* Do nothing if YYNORMAL or if *YYLOW <= YYLOW1.  Otherwise, fill in
 * YYVSP[YYLOW1 .. *YYLOW-1] as in yyfillin and set *YYLOW = YYLOW1.
 * For convenience, always return YYLOW1.  */
static inline int yyfill (yyGLRStackItem *, int *, int, yybool)
     YY_ATTRIBUTE_UNUSED;
static inline int
yyfill (yyGLRStackItem *yyvsp, int *yylow, int yylow1, yybool yynormal)
{
  if (!yynormal && yylow1 < *yylow)
    {
      yyfillin (yyvsp, *yylow, yylow1);
      *yylow = yylow1;
    }
  return yylow1;
}

/** Perform user action for rule number YYN, with RHS length YYRHSLEN,
 *  and top stack item YYVSP.  YYLVALP points to place to put semantic
 *  value ($$), and yylocp points to place for location information
 *  (@$).  Returns yyok for normal return, yyaccept for YYACCEPT,
 *  yyerr for YYERROR, yyabort for YYABORT.  */
static YYRESULTTAG
yyuserAction (yyRuleNum yyn, size_t yyrhslen, yyGLRStackItem* yyvsp,
              yyGLRStack* yystackp,
              YYSTYPE* yyvalp, yy::parser& yyparser)
{
  yybool yynormal YY_ATTRIBUTE_UNUSED = (yystackp->yysplitPoint == YY_NULLPTR);
  int yylow;
  YYUSE (yyvalp);
  YYUSE (yyparser);
  YYUSE (yyrhslen);
# undef yyerrok
# define yyerrok (yystackp->yyerrState = 0)
# undef YYACCEPT
# define YYACCEPT return yyaccept
# undef YYABORT
# define YYABORT return yyabort
# undef YYERROR
# define YYERROR return yyerrok, yyerr
# undef YYRECOVERING
# define YYRECOVERING() (yystackp->yyerrState != 0)
# undef yyclearin
# define yyclearin (yychar = YYEMPTY)
# undef YYFILL
# define YYFILL(N) yyfill (yyvsp, &yylow, N, yynormal)
# undef YYBACKUP
# define YYBACKUP(Token, Value)                                              \
  return yyerror (yyparser, YY_("syntax error: cannot back up")),     \
         yyerrok, yyerr

  yylow = 1;
  if (yyrhslen == 0)
    *yyvalp = yyval_default;
  else
    *yyvalp = yyvsp[YYFILL (1-yyrhslen)].yystate.yysemantics.yysval;
  switch (yyn)
    {
        case 3:
#line 118 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 1520 "src/parser.cpp" // glr.c:816
    break;

  case 4:
#line 119 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1526 "src/parser.cpp" // glr.c:816
    break;

  case 5:
#line 120 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 1532 "src/parser.cpp" // glr.c:816
    break;

  case 6:
#line 121 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1538 "src/parser.cpp" // glr.c:816
    break;

  case 21:
#line 149 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (Node*)lextxt;}
#line 1544 "src/parser.cpp" // glr.c:816
    break;

  case 22:
#line 152 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (Node*)lextxt;}
#line 1550 "src/parser.cpp" // glr.c:816
    break;

  case 23:
#line 155 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkIntLitNode(lextxt);}
#line 1556 "src/parser.cpp" // glr.c:816
    break;

  case 24:
#line 158 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFltLitNode(lextxt);}
#line 1562 "src/parser.cpp" // glr.c:816
    break;

  case 25:
#line 161 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkStrLitNode(lextxt);}
#line 1568 "src/parser.cpp" // glr.c:816
    break;

  case 26:
#line 164 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_I8,  (char*)"");}
#line 1574 "src/parser.cpp" // glr.c:816
    break;

  case 27:
#line 165 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_I16, (char*)"");}
#line 1580 "src/parser.cpp" // glr.c:816
    break;

  case 28:
#line 166 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_I32, (char*)"");}
#line 1586 "src/parser.cpp" // glr.c:816
    break;

  case 29:
#line 167 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_I64, (char*)"");}
#line 1592 "src/parser.cpp" // glr.c:816
    break;

  case 30:
#line 168 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_U8,  (char*)"");}
#line 1598 "src/parser.cpp" // glr.c:816
    break;

  case 31:
#line 169 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_U16, (char*)"");}
#line 1604 "src/parser.cpp" // glr.c:816
    break;

  case 32:
#line 170 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_U32, (char*)"");}
#line 1610 "src/parser.cpp" // glr.c:816
    break;

  case 33:
#line 171 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_U64, (char*)"");}
#line 1616 "src/parser.cpp" // glr.c:816
    break;

  case 34:
#line 172 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Isz, (char*)"");}
#line 1622 "src/parser.cpp" // glr.c:816
    break;

  case 35:
#line 173 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Usz, (char*)"");}
#line 1628 "src/parser.cpp" // glr.c:816
    break;

  case 36:
#line 174 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_F16, (char*)"");}
#line 1634 "src/parser.cpp" // glr.c:816
    break;

  case 37:
#line 175 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_F32, (char*)"");}
#line 1640 "src/parser.cpp" // glr.c:816
    break;

  case 38:
#line 176 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_F64, (char*)"");}
#line 1646 "src/parser.cpp" // glr.c:816
    break;

  case 39:
#line 177 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_C8,  (char*)"");}
#line 1652 "src/parser.cpp" // glr.c:816
    break;

  case 40:
#line 178 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_C32, (char*)"");}
#line 1658 "src/parser.cpp" // glr.c:816
    break;

  case 41:
#line 179 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Bool, (char*)"");}
#line 1664 "src/parser.cpp" // glr.c:816
    break;

  case 42:
#line 180 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Void, (char*)"");}
#line 1670 "src/parser.cpp" // glr.c:816
    break;

  case 43:
#line 181 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Data, (char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1676 "src/parser.cpp" // glr.c:816
    break;

  case 44:
#line 182 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_TypeVar, (char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 1682 "src/parser.cpp" // glr.c:816
    break;

  case 45:
#line 187 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Ptr,  (char*)"", (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 1688 "src/parser.cpp" // glr.c:816
    break;

  case 46:
#line 188 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Array,(char*)"", (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval));}
#line 1694 "src/parser.cpp" // glr.c:816
    break;

  case 47:
#line 189 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Func, (char*)"", (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval));}
#line 1700 "src/parser.cpp" // glr.c:816
    break;

  case 48:
#line 190 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeNode(TT_Func, (char*)"", (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval));}
#line 1706 "src/parser.cpp" // glr.c:816
    break;

  case 49:
#line 191 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval);}
#line 1712 "src/parser.cpp" // glr.c:816
    break;

  case 50:
#line 192 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 1718 "src/parser.cpp" // glr.c:816
    break;

  case 51:
#line 195 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1724 "src/parser.cpp" // glr.c:816
    break;

  case 53:
#line 197 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1730 "src/parser.cpp" // glr.c:816
    break;

  case 54:
#line 200 "src/syntax.y" // glr.c:816
    {Node* tmp = getRoot(); 
                        if(tmp == (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)){//singular type, first type in list equals the last
                            ((*yyvalp)) = tmp;
                        }else{ //tuple type
                            ((*yyvalp)) = mkTypeNode(TT_Tuple, (char*)"", tmp);
                        }
                       }
#line 1742 "src/parser.cpp" // glr.c:816
    break;

  case 55:
#line 209 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Pub);}
#line 1748 "src/parser.cpp" // glr.c:816
    break;

  case 56:
#line 210 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Pri);}
#line 1754 "src/parser.cpp" // glr.c:816
    break;

  case 57:
#line 211 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Pro);}
#line 1760 "src/parser.cpp" // glr.c:816
    break;

  case 58:
#line 212 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Raw);}
#line 1766 "src/parser.cpp" // glr.c:816
    break;

  case 59:
#line 213 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Const);}
#line 1772 "src/parser.cpp" // glr.c:816
    break;

  case 60:
#line 214 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Ext);}
#line 1778 "src/parser.cpp" // glr.c:816
    break;

  case 61:
#line 215 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Noinit);}
#line 1784 "src/parser.cpp" // glr.c:816
    break;

  case 62:
#line 216 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkModNode(Tok_Pathogen);}
#line 1790 "src/parser.cpp" // glr.c:816
    break;

  case 63:
#line 219 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1796 "src/parser.cpp" // glr.c:816
    break;

  case 64:
#line 220 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1802 "src/parser.cpp" // glr.c:816
    break;

  case 65:
#line 223 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 1808 "src/parser.cpp" // glr.c:816
    break;

  case 66:
#line 227 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1814 "src/parser.cpp" // glr.c:816
    break;

  case 67:
#line 228 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval),  0);}
#line 1820 "src/parser.cpp" // glr.c:816
    break;

  case 68:
#line 229 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1826 "src/parser.cpp" // glr.c:816
    break;

  case 69:
#line 230 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval),  0);}
#line 1832 "src/parser.cpp" // glr.c:816
    break;

  case 70:
#line 233 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1838 "src/parser.cpp" // glr.c:816
    break;

  case 71:
#line 234 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1844 "src/parser.cpp" // glr.c:816
    break;

  case 72:
#line 235 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1850 "src/parser.cpp" // glr.c:816
    break;

  case 73:
#line 236 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), 0,  0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1856 "src/parser.cpp" // glr.c:816
    break;

  case 74:
#line 240 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarAssignNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1862 "src/parser.cpp" // glr.c:816
    break;

  case 75:
#line 241 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarAssignNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), mkBinOpNode('+', mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 1868 "src/parser.cpp" // glr.c:816
    break;

  case 76:
#line 242 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarAssignNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), mkBinOpNode('-', mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 1874 "src/parser.cpp" // glr.c:816
    break;

  case 77:
#line 243 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarAssignNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), mkBinOpNode('*', mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 1880 "src/parser.cpp" // glr.c:816
    break;

  case 78:
#line 244 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarAssignNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), mkBinOpNode('/', mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 1886 "src/parser.cpp" // glr.c:816
    break;

  case 79:
#line 247 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1892 "src/parser.cpp" // glr.c:816
    break;

  case 80:
#line 248 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1898 "src/parser.cpp" // glr.c:816
    break;

  case 81:
#line 251 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 1904 "src/parser.cpp" // glr.c:816
    break;

  case 82:
#line 254 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkDataDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1910 "src/parser.cpp" // glr.c:816
    break;

  case 83:
#line 255 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkDataDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1916 "src/parser.cpp" // glr.c:816
    break;

  case 84:
#line 256 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkDataDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1922 "src/parser.cpp" // glr.c:816
    break;

  case 85:
#line 257 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkDataDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1928 "src/parser.cpp" // glr.c:816
    break;

  case 86:
#line 260 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkNamedValNode(mkVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 1934 "src/parser.cpp" // glr.c:816
    break;

  case 87:
#line 261 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkNamedValNode(0, (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1940 "src/parser.cpp" // glr.c:816
    break;

  case 89:
#line 265 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1946 "src/parser.cpp" // glr.c:816
    break;

  case 90:
#line 266 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 1952 "src/parser.cpp" // glr.c:816
    break;

  case 91:
#line 269 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 1958 "src/parser.cpp" // glr.c:816
    break;

  case 97:
#line 282 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 1964 "src/parser.cpp" // glr.c:816
    break;

  case 98:
#line 283 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 1970 "src/parser.cpp" // glr.c:816
    break;

  case 99:
#line 284 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 1976 "src/parser.cpp" // glr.c:816
    break;

  case 100:
#line 285 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 1982 "src/parser.cpp" // glr.c:816
    break;

  case 101:
#line 288 "src/syntax.y" // glr.c:816
    {setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval)); ((*yyvalp)) = getRoot();}
#line 1988 "src/parser.cpp" // glr.c:816
    break;

  case 102:
#line 289 "src/syntax.y" // glr.c:816
    {setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval)); ((*yyvalp)) = getRoot();}
#line 1994 "src/parser.cpp" // glr.c:816
    break;

  case 103:
#line 290 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval);}
#line 2000 "src/parser.cpp" // glr.c:816
    break;

  case 104:
#line 291 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval);}
#line 2006 "src/parser.cpp" // glr.c:816
    break;

  case 105:
#line 294 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), mkVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2012 "src/parser.cpp" // glr.c:816
    break;

  case 106:
#line 295 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot(mkVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2018 "src/parser.cpp" // glr.c:816
    break;

  case 107:
#line 298 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 2024 "src/parser.cpp" // glr.c:816
    break;

  case 108:
#line 305 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), mkNamedValNode((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval)));}
#line 2030 "src/parser.cpp" // glr.c:816
    break;

  case 109:
#line 306 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot(mkNamedValNode((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval)));}
#line 2036 "src/parser.cpp" // glr.c:816
    break;

  case 110:
#line 309 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 2042 "src/parser.cpp" // glr.c:816
    break;

  case 111:
#line 310 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 2048 "src/parser.cpp" // glr.c:816
    break;

  case 112:
#line 313 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2054 "src/parser.cpp" // glr.c:816
    break;

  case 113:
#line 314 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-6)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-8)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-7)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2060 "src/parser.cpp" // glr.c:816
    break;

  case 114:
#line 315 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2066 "src/parser.cpp" // glr.c:816
    break;

  case 115:
#line 316 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-6)].yystate.yysemantics.yysval), 0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-7)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2072 "src/parser.cpp" // glr.c:816
    break;

  case 116:
#line 317 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncDeclNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), 0,  0,  (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2078 "src/parser.cpp" // glr.c:816
    break;

  case 117:
#line 320 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkFuncCallNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2084 "src/parser.cpp" // glr.c:816
    break;

  case 118:
#line 323 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkRetNode((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2090 "src/parser.cpp" // glr.c:816
    break;

  case 119:
#line 326 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setElse((IfNode*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (IfNode*)mkIfNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2096 "src/parser.cpp" // glr.c:816
    break;

  case 120:
#line 327 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot(mkIfNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2102 "src/parser.cpp" // glr.c:816
    break;

  case 121:
#line 330 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setElse((IfNode*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (IfNode*)mkIfNode(NULL, (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2108 "src/parser.cpp" // glr.c:816
    break;

  case 122:
#line 331 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2114 "src/parser.cpp" // glr.c:816
    break;

  case 123:
#line 332 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot(mkIfNode(NULL, (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2120 "src/parser.cpp" // glr.c:816
    break;

  case 124:
#line 333 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot(NULL);}
#line 2126 "src/parser.cpp" // glr.c:816
    break;

  case 125:
#line 336 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkIfNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (IfNode*)getRoot());}
#line 2132 "src/parser.cpp" // glr.c:816
    break;

  case 126:
#line 339 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 2138 "src/parser.cpp" // glr.c:816
    break;

  case 127:
#line 342 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 2144 "src/parser.cpp" // glr.c:816
    break;

  case 128:
#line 345 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 2150 "src/parser.cpp" // glr.c:816
    break;

  case 129:
#line 348 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2156 "src/parser.cpp" // glr.c:816
    break;

  case 130:
#line 351 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkUnOpNode('&', (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2162 "src/parser.cpp" // glr.c:816
    break;

  case 131:
#line 352 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2168 "src/parser.cpp" // glr.c:816
    break;

  case 132:
#line 353 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('[', mkRefVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 2174 "src/parser.cpp" // glr.c:816
    break;

  case 133:
#line 354 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkRefVarNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2180 "src/parser.cpp" // glr.c:816
    break;

  case 134:
#line 357 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2186 "src/parser.cpp" // glr.c:816
    break;

  case 135:
#line 358 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval);}
#line 2192 "src/parser.cpp" // glr.c:816
    break;

  case 136:
#line 359 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2198 "src/parser.cpp" // glr.c:816
    break;

  case 137:
#line 360 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2204 "src/parser.cpp" // glr.c:816
    break;

  case 138:
#line 361 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval);}
#line 2210 "src/parser.cpp" // glr.c:816
    break;

  case 139:
#line 362 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2216 "src/parser.cpp" // glr.c:816
    break;

  case 140:
#line 363 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2222 "src/parser.cpp" // glr.c:816
    break;

  case 141:
#line 364 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2228 "src/parser.cpp" // glr.c:816
    break;

  case 142:
#line 365 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2234 "src/parser.cpp" // glr.c:816
    break;

  case 143:
#line 366 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2240 "src/parser.cpp" // glr.c:816
    break;

  case 144:
#line 367 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBoolLitNode(1);}
#line 2246 "src/parser.cpp" // glr.c:816
    break;

  case 145:
#line 368 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBoolLitNode(0);}
#line 2252 "src/parser.cpp" // glr.c:816
    break;

  case 146:
#line 371 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTupleNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 2258 "src/parser.cpp" // glr.c:816
    break;

  case 147:
#line 372 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTupleNode(0);}
#line 2264 "src/parser.cpp" // glr.c:816
    break;

  case 148:
#line 375 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkArrayNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 2270 "src/parser.cpp" // glr.c:816
    break;

  case 149:
#line 376 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkArrayNode(0);}
#line 2276 "src/parser.cpp" // glr.c:816
    break;

  case 150:
#line 379 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2282 "src/parser.cpp" // glr.c:816
    break;

  case 151:
#line 380 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = NULL;}
#line 2288 "src/parser.cpp" // glr.c:816
    break;

  case 152:
#line 383 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 2294 "src/parser.cpp" // glr.c:816
    break;

  case 153:
#line 386 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2300 "src/parser.cpp" // glr.c:816
    break;

  case 154:
#line 387 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2306 "src/parser.cpp" // glr.c:816
    break;

  case 155:
#line 392 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkUnOpNode('@', (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2312 "src/parser.cpp" // glr.c:816
    break;

  case 156:
#line 393 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkUnOpNode('&', (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2318 "src/parser.cpp" // glr.c:816
    break;

  case 157:
#line 394 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkUnOpNode('-', (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2324 "src/parser.cpp" // glr.c:816
    break;

  case 158:
#line 395 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkTypeCastNode((((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2330 "src/parser.cpp" // glr.c:816
    break;

  case 159:
#line 398 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2336 "src/parser.cpp" // glr.c:816
    break;

  case 160:
#line 401 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('+', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2342 "src/parser.cpp" // glr.c:816
    break;

  case 161:
#line 402 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('-', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2348 "src/parser.cpp" // glr.c:816
    break;

  case 162:
#line 403 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('*', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2354 "src/parser.cpp" // glr.c:816
    break;

  case 163:
#line 404 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('/', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2360 "src/parser.cpp" // glr.c:816
    break;

  case 164:
#line 405 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('%', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2366 "src/parser.cpp" // glr.c:816
    break;

  case 165:
#line 406 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('<', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2372 "src/parser.cpp" // glr.c:816
    break;

  case 166:
#line 407 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('>', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2378 "src/parser.cpp" // glr.c:816
    break;

  case 167:
#line 408 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('^', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2384 "src/parser.cpp" // glr.c:816
    break;

  case 168:
#line 409 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('.', (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2390 "src/parser.cpp" // glr.c:816
    break;

  case 169:
#line 410 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(';', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2396 "src/parser.cpp" // glr.c:816
    break;

  case 170:
#line 411 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('[', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-1)].yystate.yysemantics.yysval));}
#line 2402 "src/parser.cpp" // glr.c:816
    break;

  case 171:
#line 412 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Where, (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), 0, 0, (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2408 "src/parser.cpp" // glr.c:816
    break;

  case 172:
#line 413 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Let, mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), 0, 0, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2414 "src/parser.cpp" // glr.c:816
    break;

  case 173:
#line 414 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Eq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2420 "src/parser.cpp" // glr.c:816
    break;

  case 174:
#line 415 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_NotEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2426 "src/parser.cpp" // glr.c:816
    break;

  case 175:
#line 416 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_GrtrEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2432 "src/parser.cpp" // glr.c:816
    break;

  case 176:
#line 417 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_LesrEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2438 "src/parser.cpp" // glr.c:816
    break;

  case 177:
#line 418 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Or, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2444 "src/parser.cpp" // glr.c:816
    break;

  case 178:
#line 419 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_And, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2450 "src/parser.cpp" // glr.c:816
    break;

  case 179:
#line 420 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Range, (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2456 "src/parser.cpp" // glr.c:816
    break;

  case 180:
#line 421 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2462 "src/parser.cpp" // glr.c:816
    break;

  case 181:
#line 426 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = getRoot();}
#line 2468 "src/parser.cpp" // glr.c:816
    break;

  case 182:
#line 429 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setNext((((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2474 "src/parser.cpp" // glr.c:816
    break;

  case 183:
#line 430 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = setRoot((((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2480 "src/parser.cpp" // glr.c:816
    break;

  case 184:
#line 433 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('+', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2486 "src/parser.cpp" // glr.c:816
    break;

  case 185:
#line 434 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('-', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2492 "src/parser.cpp" // glr.c:816
    break;

  case 186:
#line 435 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('*', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2498 "src/parser.cpp" // glr.c:816
    break;

  case 187:
#line 436 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('/', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2504 "src/parser.cpp" // glr.c:816
    break;

  case 188:
#line 437 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('%', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2510 "src/parser.cpp" // glr.c:816
    break;

  case 189:
#line 438 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('<', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2516 "src/parser.cpp" // glr.c:816
    break;

  case 190:
#line 439 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('>', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2522 "src/parser.cpp" // glr.c:816
    break;

  case 191:
#line 440 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('^', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2528 "src/parser.cpp" // glr.c:816
    break;

  case 192:
#line 441 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('.', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2534 "src/parser.cpp" // glr.c:816
    break;

  case 193:
#line 442 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(';', (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2540 "src/parser.cpp" // glr.c:816
    break;

  case 194:
#line 443 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode('[', (((yyGLRStackItem const *)yyvsp)[YYFILL (-4)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (-2)].yystate.yysemantics.yysval));}
#line 2546 "src/parser.cpp" // glr.c:816
    break;

  case 195:
#line 444 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Where, (((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval), mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), 0, 0, (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval)));}
#line 2552 "src/parser.cpp" // glr.c:816
    break;

  case 196:
#line 445 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Let, mkLetBindingNode((char*)(((yyGLRStackItem const *)yyvsp)[YYFILL (-5)].yystate.yysemantics.yysval), 0, 0, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval)), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2558 "src/parser.cpp" // glr.c:816
    break;

  case 197:
#line 446 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Eq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2564 "src/parser.cpp" // glr.c:816
    break;

  case 198:
#line 447 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_NotEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2570 "src/parser.cpp" // glr.c:816
    break;

  case 199:
#line 448 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_GrtrEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2576 "src/parser.cpp" // glr.c:816
    break;

  case 200:
#line 449 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_LesrEq, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2582 "src/parser.cpp" // glr.c:816
    break;

  case 201:
#line 450 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_Or, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2588 "src/parser.cpp" // glr.c:816
    break;

  case 202:
#line 451 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = mkBinOpNode(Tok_And, (((yyGLRStackItem const *)yyvsp)[YYFILL (-3)].yystate.yysemantics.yysval), (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval));}
#line 2594 "src/parser.cpp" // glr.c:816
    break;

  case 203:
#line 452 "src/syntax.y" // glr.c:816
    {((*yyvalp)) = (((yyGLRStackItem const *)yyvsp)[YYFILL (0)].yystate.yysemantics.yysval);}
#line 2600 "src/parser.cpp" // glr.c:816
    break;


#line 2604 "src/parser.cpp" // glr.c:816
      default: break;
    }

  return yyok;
# undef yyerrok
# undef YYABORT
# undef YYACCEPT
# undef YYERROR
# undef YYBACKUP
# undef yyclearin
# undef YYRECOVERING
}


static void
yyuserMerge (int yyn, YYSTYPE* yy0, YYSTYPE* yy1)
{
  YYUSE (yy0);
  YYUSE (yy1);

  switch (yyn)
    {

      default: break;
    }
}

                              /* Bison grammar-table manipulation.  */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, yy::parser& yyparser)
{
  YYUSE (yyvaluep);
  YYUSE (yyparser);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}

/** Number of symbols composing the right hand side of rule #RULE.  */
static inline int
yyrhsLength (yyRuleNum yyrule)
{
  return yyr2[yyrule];
}

static void
yydestroyGLRState (char const *yymsg, yyGLRState *yys, yy::parser& yyparser)
{
  if (yys->yyresolved)
    yydestruct (yymsg, yystos[yys->yylrState],
                &yys->yysemantics.yysval, yyparser);
  else
    {
#if YYDEBUG
      if (yydebug)
        {
          if (yys->yysemantics.yyfirstVal)
            YYFPRINTF (stderr, "%s unresolved", yymsg);
          else
            YYFPRINTF (stderr, "%s incomplete", yymsg);
          YY_SYMBOL_PRINT ("", yystos[yys->yylrState], YY_NULLPTR, &yys->yyloc);
        }
#endif

      if (yys->yysemantics.yyfirstVal)
        {
          yySemanticOption *yyoption = yys->yysemantics.yyfirstVal;
          yyGLRState *yyrh;
          int yyn;
          for (yyrh = yyoption->yystate, yyn = yyrhsLength (yyoption->yyrule);
               yyn > 0;
               yyrh = yyrh->yypred, yyn -= 1)
            yydestroyGLRState (yymsg, yyrh, yyparser);
        }
    }
}

/** Left-hand-side symbol for rule #YYRULE.  */
static inline yySymbol
yylhsNonterm (yyRuleNum yyrule)
{
  return yyr1[yyrule];
}

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-171)))

/** True iff LR state YYSTATE has only a default reduction (regardless
 *  of token).  */
static inline yybool
yyisDefaultedState (yyStateNum yystate)
{
  return yypact_value_is_default (yypact[yystate]);
}

/** The default reduction for YYSTATE, assuming it has one.  */
static inline yyRuleNum
yydefaultAction (yyStateNum yystate)
{
  return yydefact[yystate];
}

#define yytable_value_is_error(Yytable_value) \
  0

/** Set *YYACTION to the action to take in YYSTATE on seeing YYTOKEN.
 *  Result R means
 *    R < 0:  Reduce on rule -R.
 *    R = 0:  Error.
 *    R > 0:  Shift to state R.
 *  Set *YYCONFLICTS to a pointer into yyconfl to a 0-terminated list
 *  of conflicting reductions.
 */
static inline void
yygetLRActions (yyStateNum yystate, int yytoken,
                int* yyaction, const short int** yyconflicts)
{
  int yyindex = yypact[yystate] + yytoken;
  if (yypact_value_is_default (yypact[yystate])
      || yyindex < 0 || YYLAST < yyindex || yycheck[yyindex] != yytoken)
    {
      *yyaction = -yydefact[yystate];
      *yyconflicts = yyconfl;
    }
  else if (! yytable_value_is_error (yytable[yyindex]))
    {
      *yyaction = yytable[yyindex];
      *yyconflicts = yyconfl + yyconflp[yyindex];
    }
  else
    {
      *yyaction = 0;
      *yyconflicts = yyconfl + yyconflp[yyindex];
    }
}

/** Compute post-reduction state.
 * \param yystate   the current state
 * \param yysym     the nonterminal to push on the stack
 */
static inline yyStateNum
yyLRgotoState (yyStateNum yystate, yySymbol yysym)
{
  int yyr = yypgoto[yysym - YYNTOKENS] + yystate;
  if (0 <= yyr && yyr <= YYLAST && yycheck[yyr] == yystate)
    return yytable[yyr];
  else
    return yydefgoto[yysym - YYNTOKENS];
}

static inline yybool
yyisShiftAction (int yyaction)
{
  return 0 < yyaction;
}

static inline yybool
yyisErrorAction (int yyaction)
{
  return yyaction == 0;
}

                                /* GLRStates */

/** Return a fresh GLRStackItem in YYSTACKP.  The item is an LR state
 *  if YYISSTATE, and otherwise a semantic option.  Callers should call
 *  YY_RESERVE_GLRSTACK afterwards to make sure there is sufficient
 *  headroom.  */

static inline yyGLRStackItem*
yynewGLRStackItem (yyGLRStack* yystackp, yybool yyisState)
{
  yyGLRStackItem* yynewItem = yystackp->yynextFree;
  yystackp->yyspaceLeft -= 1;
  yystackp->yynextFree += 1;
  yynewItem->yystate.yyisState = yyisState;
  return yynewItem;
}

/** Add a new semantic action that will execute the action for rule
 *  YYRULE on the semantic values in YYRHS to the list of
 *  alternative actions for YYSTATE.  Assumes that YYRHS comes from
 *  stack #YYK of *YYSTACKP. */
static void
yyaddDeferredAction (yyGLRStack* yystackp, size_t yyk, yyGLRState* yystate,
                     yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yySemanticOption* yynewOption =
    &yynewGLRStackItem (yystackp, yyfalse)->yyoption;
  YYASSERT (!yynewOption->yyisState);
  yynewOption->yystate = yyrhs;
  yynewOption->yyrule = yyrule;
  if (yystackp->yytops.yylookaheadNeeds[yyk])
    {
      yynewOption->yyrawchar = yychar;
      yynewOption->yyval = yylval;
    }
  else
    yynewOption->yyrawchar = YYEMPTY;
  yynewOption->yynext = yystate->yysemantics.yyfirstVal;
  yystate->yysemantics.yyfirstVal = yynewOption;

  YY_RESERVE_GLRSTACK (yystackp);
}

                                /* GLRStacks */

/** Initialize YYSET to a singleton set containing an empty stack.  */
static yybool
yyinitStateSet (yyGLRStateSet* yyset)
{
  yyset->yysize = 1;
  yyset->yycapacity = 16;
  yyset->yystates = (yyGLRState**) YYMALLOC (16 * sizeof yyset->yystates[0]);
  if (! yyset->yystates)
    return yyfalse;
  yyset->yystates[0] = YY_NULLPTR;
  yyset->yylookaheadNeeds =
    (yybool*) YYMALLOC (16 * sizeof yyset->yylookaheadNeeds[0]);
  if (! yyset->yylookaheadNeeds)
    {
      YYFREE (yyset->yystates);
      return yyfalse;
    }
  return yytrue;
}

static void yyfreeStateSet (yyGLRStateSet* yyset)
{
  YYFREE (yyset->yystates);
  YYFREE (yyset->yylookaheadNeeds);
}

/** Initialize *YYSTACKP to a single empty stack, with total maximum
 *  capacity for all stacks of YYSIZE.  */
static yybool
yyinitGLRStack (yyGLRStack* yystackp, size_t yysize)
{
  yystackp->yyerrState = 0;
  yynerrs = 0;
  yystackp->yyspaceLeft = yysize;
  yystackp->yyitems =
    (yyGLRStackItem*) YYMALLOC (yysize * sizeof yystackp->yynextFree[0]);
  if (!yystackp->yyitems)
    return yyfalse;
  yystackp->yynextFree = yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;
  return yyinitStateSet (&yystackp->yytops);
}


#if YYSTACKEXPANDABLE
# define YYRELOC(YYFROMITEMS,YYTOITEMS,YYX,YYTYPE) \
  &((YYTOITEMS) - ((YYFROMITEMS) - (yyGLRStackItem*) (YYX)))->YYTYPE

/** If *YYSTACKP is expandable, extend it.  WARNING: Pointers into the
    stack from outside should be considered invalid after this call.
    We always expand when there are 1 or fewer items left AFTER an
    allocation, so that we can avoid having external pointers exist
    across an allocation.  */
static void
yyexpandGLRStack (yyGLRStack* yystackp)
{
  yyGLRStackItem* yynewItems;
  yyGLRStackItem* yyp0, *yyp1;
  size_t yynewSize;
  size_t yyn;
  size_t yysize = yystackp->yynextFree - yystackp->yyitems;
  if (YYMAXDEPTH - YYHEADROOM < yysize)
    yyMemoryExhausted (yystackp);
  yynewSize = 2*yysize;
  if (YYMAXDEPTH < yynewSize)
    yynewSize = YYMAXDEPTH;
  yynewItems = (yyGLRStackItem*) YYMALLOC (yynewSize * sizeof yynewItems[0]);
  if (! yynewItems)
    yyMemoryExhausted (yystackp);
  for (yyp0 = yystackp->yyitems, yyp1 = yynewItems, yyn = yysize;
       0 < yyn;
       yyn -= 1, yyp0 += 1, yyp1 += 1)
    {
      *yyp1 = *yyp0;
      if (*(yybool *) yyp0)
        {
          yyGLRState* yys0 = &yyp0->yystate;
          yyGLRState* yys1 = &yyp1->yystate;
          if (yys0->yypred != YY_NULLPTR)
            yys1->yypred =
              YYRELOC (yyp0, yyp1, yys0->yypred, yystate);
          if (! yys0->yyresolved && yys0->yysemantics.yyfirstVal != YY_NULLPTR)
            yys1->yysemantics.yyfirstVal =
              YYRELOC (yyp0, yyp1, yys0->yysemantics.yyfirstVal, yyoption);
        }
      else
        {
          yySemanticOption* yyv0 = &yyp0->yyoption;
          yySemanticOption* yyv1 = &yyp1->yyoption;
          if (yyv0->yystate != YY_NULLPTR)
            yyv1->yystate = YYRELOC (yyp0, yyp1, yyv0->yystate, yystate);
          if (yyv0->yynext != YY_NULLPTR)
            yyv1->yynext = YYRELOC (yyp0, yyp1, yyv0->yynext, yyoption);
        }
    }
  if (yystackp->yysplitPoint != YY_NULLPTR)
    yystackp->yysplitPoint = YYRELOC (yystackp->yyitems, yynewItems,
                                      yystackp->yysplitPoint, yystate);

  for (yyn = 0; yyn < yystackp->yytops.yysize; yyn += 1)
    if (yystackp->yytops.yystates[yyn] != YY_NULLPTR)
      yystackp->yytops.yystates[yyn] =
        YYRELOC (yystackp->yyitems, yynewItems,
                 yystackp->yytops.yystates[yyn], yystate);
  YYFREE (yystackp->yyitems);
  yystackp->yyitems = yynewItems;
  yystackp->yynextFree = yynewItems + yysize;
  yystackp->yyspaceLeft = yynewSize - yysize;
}
#endif

static void
yyfreeGLRStack (yyGLRStack* yystackp)
{
  YYFREE (yystackp->yyitems);
  yyfreeStateSet (&yystackp->yytops);
}

/** Assuming that YYS is a GLRState somewhere on *YYSTACKP, update the
 *  splitpoint of *YYSTACKP, if needed, so that it is at least as deep as
 *  YYS.  */
static inline void
yyupdateSplit (yyGLRStack* yystackp, yyGLRState* yys)
{
  if (yystackp->yysplitPoint != YY_NULLPTR && yystackp->yysplitPoint > yys)
    yystackp->yysplitPoint = yys;
}

/** Invalidate stack #YYK in *YYSTACKP.  */
static inline void
yymarkStackDeleted (yyGLRStack* yystackp, size_t yyk)
{
  if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    yystackp->yylastDeleted = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yystates[yyk] = YY_NULLPTR;
}

/** Undelete the last stack in *YYSTACKP that was marked as deleted.  Can
    only be done once after a deletion, and only when all other stacks have
    been deleted.  */
static void
yyundeleteLastStack (yyGLRStack* yystackp)
{
  if (yystackp->yylastDeleted == YY_NULLPTR || yystackp->yytops.yysize != 0)
    return;
  yystackp->yytops.yystates[0] = yystackp->yylastDeleted;
  yystackp->yytops.yysize = 1;
  YYDPRINTF ((stderr, "Restoring last deleted stack as stack #0.\n"));
  yystackp->yylastDeleted = YY_NULLPTR;
}

static inline void
yyremoveDeletes (yyGLRStack* yystackp)
{
  size_t yyi, yyj;
  yyi = yyj = 0;
  while (yyj < yystackp->yytops.yysize)
    {
      if (yystackp->yytops.yystates[yyi] == YY_NULLPTR)
        {
          if (yyi == yyj)
            {
              YYDPRINTF ((stderr, "Removing dead stacks.\n"));
            }
          yystackp->yytops.yysize -= 1;
        }
      else
        {
          yystackp->yytops.yystates[yyj] = yystackp->yytops.yystates[yyi];
          /* In the current implementation, it's unnecessary to copy
             yystackp->yytops.yylookaheadNeeds[yyi] since, after
             yyremoveDeletes returns, the parser immediately either enters
             deterministic operation or shifts a token.  However, it doesn't
             hurt, and the code might evolve to need it.  */
          yystackp->yytops.yylookaheadNeeds[yyj] =
            yystackp->yytops.yylookaheadNeeds[yyi];
          if (yyj != yyi)
            {
              YYDPRINTF ((stderr, "Rename stack %lu -> %lu.\n",
                          (unsigned long int) yyi, (unsigned long int) yyj));
            }
          yyj += 1;
        }
      yyi += 1;
    }
}

/** Shift to a new state on stack #YYK of *YYSTACKP, corresponding to LR
 * state YYLRSTATE, at input position YYPOSN, with (resolved) semantic
 * value *YYVALP and source location *YYLOCP.  */
static inline void
yyglrShift (yyGLRStack* yystackp, size_t yyk, yyStateNum yylrState,
            size_t yyposn,
            YYSTYPE* yyvalp)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yytrue;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yysval = *yyvalp;
  yystackp->yytops.yystates[yyk] = yynewState;

  YY_RESERVE_GLRSTACK (yystackp);
}

/** Shift stack #YYK of *YYSTACKP, to a new state corresponding to LR
 *  state YYLRSTATE, at input position YYPOSN, with the (unresolved)
 *  semantic value of YYRHS under the action for YYRULE.  */
static inline void
yyglrShiftDefer (yyGLRStack* yystackp, size_t yyk, yyStateNum yylrState,
                 size_t yyposn, yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;
  YYASSERT (yynewState->yyisState);

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yyfalse;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yyfirstVal = YY_NULLPTR;
  yystackp->yytops.yystates[yyk] = yynewState;

  /* Invokes YY_RESERVE_GLRSTACK.  */
  yyaddDeferredAction (yystackp, yyk, yynewState, yyrhs, yyrule);
}

#if !YYDEBUG
# define YY_REDUCE_PRINT(Args)
#else
# define YY_REDUCE_PRINT(Args)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print Args;               \
} while (0)

/*----------------------------------------------------------------------.
| Report that stack #YYK of *YYSTACKP is going to be reduced by YYRULE. |
`----------------------------------------------------------------------*/

static inline void
yy_reduce_print (int yynormal, yyGLRStackItem* yyvsp, size_t yyk,
                 yyRuleNum yyrule, yy::parser& yyparser)
{
  int yynrhs = yyrhsLength (yyrule);
  int yyi;
  YYFPRINTF (stderr, "Reducing stack %lu by rule %d (line %lu):\n",
             (unsigned long int) yyk, yyrule - 1,
             (unsigned long int) yyrline[yyrule]);
  if (! yynormal)
    yyfillin (yyvsp, 1, -yynrhs);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyvsp[yyi - yynrhs + 1].yystate.yylrState],
                       &yyvsp[yyi - yynrhs + 1].yystate.yysemantics.yysval
                                              , yyparser);
      if (!yyvsp[yyi - yynrhs + 1].yystate.yyresolved)
        YYFPRINTF (stderr, " (unresolved)");
      YYFPRINTF (stderr, "\n");
    }
}
#endif

/** Pop the symbols consumed by reduction #YYRULE from the top of stack
 *  #YYK of *YYSTACKP, and perform the appropriate semantic action on their
 *  semantic values.  Assumes that all ambiguities in semantic values
 *  have been previously resolved.  Set *YYVALP to the resulting value,
 *  and *YYLOCP to the computed location (if any).  Return value is as
 *  for userAction.  */
static inline YYRESULTTAG
yydoAction (yyGLRStack* yystackp, size_t yyk, yyRuleNum yyrule,
            YYSTYPE* yyvalp, yy::parser& yyparser)
{
  int yynrhs = yyrhsLength (yyrule);

  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      /* Standard special case: single stack.  */
      yyGLRStackItem* yyrhs = (yyGLRStackItem*) yystackp->yytops.yystates[yyk];
      YYASSERT (yyk == 0);
      yystackp->yynextFree -= yynrhs;
      yystackp->yyspaceLeft += yynrhs;
      yystackp->yytops.yystates[0] = & yystackp->yynextFree[-1].yystate;
      YY_REDUCE_PRINT ((1, yyrhs, yyk, yyrule, yyparser));
      return yyuserAction (yyrule, yynrhs, yyrhs, yystackp,
                           yyvalp, yyparser);
    }
  else
    {
      int yyi;
      yyGLRState* yys;
      yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
      yys = yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred
        = yystackp->yytops.yystates[yyk];
      for (yyi = 0; yyi < yynrhs; yyi += 1)
        {
          yys = yys->yypred;
          YYASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yystackp->yytops.yystates[yyk] = yys;
      YY_REDUCE_PRINT ((0, yyrhsVals + YYMAXRHS + YYMAXLEFT - 1, yyk, yyrule, yyparser));
      return yyuserAction (yyrule, yynrhs, yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, yyvalp, yyparser);
    }
}

/** Pop items off stack #YYK of *YYSTACKP according to grammar rule YYRULE,
 *  and push back on the resulting nonterminal symbol.  Perform the
 *  semantic action associated with YYRULE and store its value with the
 *  newly pushed state, if YYFORCEEVAL or if *YYSTACKP is currently
 *  unambiguous.  Otherwise, store the deferred semantic action with
 *  the new state.  If the new state would have an identical input
 *  position, LR state, and predecessor to an existing state on the stack,
 *  it is identified with that existing state, eliminating stack #YYK from
 *  *YYSTACKP.  In this case, the semantic value is
 *  added to the options for the existing state's semantic value.
 */
static inline YYRESULTTAG
yyglrReduce (yyGLRStack* yystackp, size_t yyk, yyRuleNum yyrule,
             yybool yyforceEval, yy::parser& yyparser)
{
  size_t yyposn = yystackp->yytops.yystates[yyk]->yyposn;

  if (yyforceEval || yystackp->yysplitPoint == YY_NULLPTR)
    {
      YYSTYPE yysval;

      YYRESULTTAG yyflag = yydoAction (yystackp, yyk, yyrule, &yysval, yyparser);
      if (yyflag == yyerr && yystackp->yysplitPoint != YY_NULLPTR)
        {
          YYDPRINTF ((stderr, "Parse on stack %lu rejected by rule #%d.\n",
                     (unsigned long int) yyk, yyrule - 1));
        }
      if (yyflag != yyok)
        return yyflag;
      YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyrule], &yysval, &yyloc);
      yyglrShift (yystackp, yyk,
                  yyLRgotoState (yystackp->yytops.yystates[yyk]->yylrState,
                                 yylhsNonterm (yyrule)),
                  yyposn, &yysval);
    }
  else
    {
      size_t yyi;
      int yyn;
      yyGLRState* yys, *yys0 = yystackp->yytops.yystates[yyk];
      yyStateNum yynewLRState;

      for (yys = yystackp->yytops.yystates[yyk], yyn = yyrhsLength (yyrule);
           0 < yyn; yyn -= 1)
        {
          yys = yys->yypred;
          YYASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yynewLRState = yyLRgotoState (yys->yylrState, yylhsNonterm (yyrule));
      YYDPRINTF ((stderr,
                  "Reduced stack %lu by rule #%d; action deferred.  "
                  "Now in state %d.\n",
                  (unsigned long int) yyk, yyrule - 1, yynewLRState));
      for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
        if (yyi != yyk && yystackp->yytops.yystates[yyi] != YY_NULLPTR)
          {
            yyGLRState *yysplit = yystackp->yysplitPoint;
            yyGLRState *yyp = yystackp->yytops.yystates[yyi];
            while (yyp != yys && yyp != yysplit && yyp->yyposn >= yyposn)
              {
                if (yyp->yylrState == yynewLRState && yyp->yypred == yys)
                  {
                    yyaddDeferredAction (yystackp, yyk, yyp, yys0, yyrule);
                    yymarkStackDeleted (yystackp, yyk);
                    YYDPRINTF ((stderr, "Merging stack %lu into stack %lu.\n",
                                (unsigned long int) yyk,
                                (unsigned long int) yyi));
                    return yyok;
                  }
                yyp = yyp->yypred;
              }
          }
      yystackp->yytops.yystates[yyk] = yys;
      yyglrShiftDefer (yystackp, yyk, yynewLRState, yyposn, yys0, yyrule);
    }
  return yyok;
}

static size_t
yysplitStack (yyGLRStack* yystackp, size_t yyk)
{
  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      YYASSERT (yyk == 0);
      yystackp->yysplitPoint = yystackp->yytops.yystates[yyk];
    }
  if (yystackp->yytops.yysize >= yystackp->yytops.yycapacity)
    {
      yyGLRState** yynewStates;
      yybool* yynewLookaheadNeeds;

      yynewStates = YY_NULLPTR;

      if (yystackp->yytops.yycapacity
          > (YYSIZEMAX / (2 * sizeof yynewStates[0])))
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yycapacity *= 2;

      yynewStates =
        (yyGLRState**) YYREALLOC (yystackp->yytops.yystates,
                                  (yystackp->yytops.yycapacity
                                   * sizeof yynewStates[0]));
      if (yynewStates == YY_NULLPTR)
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yystates = yynewStates;

      yynewLookaheadNeeds =
        (yybool*) YYREALLOC (yystackp->yytops.yylookaheadNeeds,
                             (yystackp->yytops.yycapacity
                              * sizeof yynewLookaheadNeeds[0]));
      if (yynewLookaheadNeeds == YY_NULLPTR)
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yylookaheadNeeds = yynewLookaheadNeeds;
    }
  yystackp->yytops.yystates[yystackp->yytops.yysize]
    = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yylookaheadNeeds[yystackp->yytops.yysize]
    = yystackp->yytops.yylookaheadNeeds[yyk];
  yystackp->yytops.yysize += 1;
  return yystackp->yytops.yysize-1;
}

/** True iff YYY0 and YYY1 represent identical options at the top level.
 *  That is, they represent the same rule applied to RHS symbols
 *  that produce the same terminal symbols.  */
static yybool
yyidenticalOptions (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  if (yyy0->yyrule == yyy1->yyrule)
    {
      yyGLRState *yys0, *yys1;
      int yyn;
      for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
           yyn = yyrhsLength (yyy0->yyrule);
           yyn > 0;
           yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
        if (yys0->yyposn != yys1->yyposn)
          return yyfalse;
      return yytrue;
    }
  else
    return yyfalse;
}

/** Assuming identicalOptions (YYY0,YYY1), destructively merge the
 *  alternative semantic values for the RHS-symbols of YYY1 and YYY0.  */
static void
yymergeOptionSets (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  yyGLRState *yys0, *yys1;
  int yyn;
  for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
       yyn = yyrhsLength (yyy0->yyrule);
       yyn > 0;
       yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
    {
      if (yys0 == yys1)
        break;
      else if (yys0->yyresolved)
        {
          yys1->yyresolved = yytrue;
          yys1->yysemantics.yysval = yys0->yysemantics.yysval;
        }
      else if (yys1->yyresolved)
        {
          yys0->yyresolved = yytrue;
          yys0->yysemantics.yysval = yys1->yysemantics.yysval;
        }
      else
        {
          yySemanticOption** yyz0p = &yys0->yysemantics.yyfirstVal;
          yySemanticOption* yyz1 = yys1->yysemantics.yyfirstVal;
          while (yytrue)
            {
              if (yyz1 == *yyz0p || yyz1 == YY_NULLPTR)
                break;
              else if (*yyz0p == YY_NULLPTR)
                {
                  *yyz0p = yyz1;
                  break;
                }
              else if (*yyz0p < yyz1)
                {
                  yySemanticOption* yyz = *yyz0p;
                  *yyz0p = yyz1;
                  yyz1 = yyz1->yynext;
                  (*yyz0p)->yynext = yyz;
                }
              yyz0p = &(*yyz0p)->yynext;
            }
          yys1->yysemantics.yyfirstVal = yys0->yysemantics.yyfirstVal;
        }
    }
}

/** Y0 and Y1 represent two possible actions to take in a given
 *  parsing state; return 0 if no combination is possible,
 *  1 if user-mergeable, 2 if Y0 is preferred, 3 if Y1 is preferred.  */
static int
yypreference (yySemanticOption* y0, yySemanticOption* y1)
{
  yyRuleNum r0 = y0->yyrule, r1 = y1->yyrule;
  int p0 = yydprec[r0], p1 = yydprec[r1];

  if (p0 == p1)
    {
      if (yymerger[r0] == 0 || yymerger[r0] != yymerger[r1])
        return 0;
      else
        return 1;
    }
  if (p0 == 0 || p1 == 0)
    return 0;
  if (p0 < p1)
    return 3;
  if (p1 < p0)
    return 2;
  return 0;
}

static YYRESULTTAG yyresolveValue (yyGLRState* yys,
                                   yyGLRStack* yystackp, yy::parser& yyparser);


/** Resolve the previous YYN states starting at and including state YYS
 *  on *YYSTACKP. If result != yyok, some states may have been left
 *  unresolved possibly with empty semantic option chains.  Regardless
 *  of whether result = yyok, each state has been left with consistent
 *  data so that yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveStates (yyGLRState* yys, int yyn,
                 yyGLRStack* yystackp, yy::parser& yyparser)
{
  if (0 < yyn)
    {
      YYASSERT (yys->yypred);
      YYCHK (yyresolveStates (yys->yypred, yyn-1, yystackp, yyparser));
      if (! yys->yyresolved)
        YYCHK (yyresolveValue (yys, yystackp, yyparser));
    }
  return yyok;
}

/** Resolve the states for the RHS of YYOPT on *YYSTACKP, perform its
 *  user action, and return the semantic value and location in *YYVALP
 *  and *YYLOCP.  Regardless of whether result = yyok, all RHS states
 *  have been destroyed (assuming the user action destroys all RHS
 *  semantic values if invoked).  */
static YYRESULTTAG
yyresolveAction (yySemanticOption* yyopt, yyGLRStack* yystackp,
                 YYSTYPE* yyvalp, yy::parser& yyparser)
{
  yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
  int yynrhs = yyrhsLength (yyopt->yyrule);
  YYRESULTTAG yyflag =
    yyresolveStates (yyopt->yystate, yynrhs, yystackp, yyparser);
  if (yyflag != yyok)
    {
      yyGLRState *yys;
      for (yys = yyopt->yystate; yynrhs > 0; yys = yys->yypred, yynrhs -= 1)
        yydestroyGLRState ("Cleanup: popping", yys, yyparser);
      return yyflag;
    }

  yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred = yyopt->yystate;
  {
    int yychar_current = yychar;
    YYSTYPE yylval_current = yylval;
    yychar = yyopt->yyrawchar;
    yylval = yyopt->yyval;
    yyflag = yyuserAction (yyopt->yyrule, yynrhs,
                           yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, yyvalp, yyparser);
    yychar = yychar_current;
    yylval = yylval_current;
  }
  return yyflag;
}

#if YYDEBUG
static void
yyreportTree (yySemanticOption* yyx, int yyindent)
{
  int yynrhs = yyrhsLength (yyx->yyrule);
  int yyi;
  yyGLRState* yys;
  yyGLRState* yystates[1 + YYMAXRHS];
  yyGLRState yyleftmost_state;

  for (yyi = yynrhs, yys = yyx->yystate; 0 < yyi; yyi -= 1, yys = yys->yypred)
    yystates[yyi] = yys;
  if (yys == YY_NULLPTR)
    {
      yyleftmost_state.yyposn = 0;
      yystates[0] = &yyleftmost_state;
    }
  else
    yystates[0] = yys;

  if (yyx->yystate->yyposn < yys->yyposn + 1)
    YYFPRINTF (stderr, "%*s%s -> <Rule %d, empty>\n",
               yyindent, "", yytokenName (yylhsNonterm (yyx->yyrule)),
               yyx->yyrule - 1);
  else
    YYFPRINTF (stderr, "%*s%s -> <Rule %d, tokens %lu .. %lu>\n",
               yyindent, "", yytokenName (yylhsNonterm (yyx->yyrule)),
               yyx->yyrule - 1, (unsigned long int) (yys->yyposn + 1),
               (unsigned long int) yyx->yystate->yyposn);
  for (yyi = 1; yyi <= yynrhs; yyi += 1)
    {
      if (yystates[yyi]->yyresolved)
        {
          if (yystates[yyi-1]->yyposn+1 > yystates[yyi]->yyposn)
            YYFPRINTF (stderr, "%*s%s <empty>\n", yyindent+2, "",
                       yytokenName (yystos[yystates[yyi]->yylrState]));
          else
            YYFPRINTF (stderr, "%*s%s <tokens %lu .. %lu>\n", yyindent+2, "",
                       yytokenName (yystos[yystates[yyi]->yylrState]),
                       (unsigned long int) (yystates[yyi-1]->yyposn + 1),
                       (unsigned long int) yystates[yyi]->yyposn);
        }
      else
        yyreportTree (yystates[yyi]->yysemantics.yyfirstVal, yyindent+2);
    }
}
#endif

static YYRESULTTAG
yyreportAmbiguity (yySemanticOption* yyx0,
                   yySemanticOption* yyx1, yy::parser& yyparser)
{
  YYUSE (yyx0);
  YYUSE (yyx1);

#if YYDEBUG
  YYFPRINTF (stderr, "Ambiguity detected.\n");
  YYFPRINTF (stderr, "Option 1,\n");
  yyreportTree (yyx0, 2);
  YYFPRINTF (stderr, "\nOption 2,\n");
  yyreportTree (yyx1, 2);
  YYFPRINTF (stderr, "\n");
#endif

  yyerror (yyparser, YY_("syntax is ambiguous"));
  return yyabort;
}

/** Resolve the ambiguity represented in state YYS in *YYSTACKP,
 *  perform the indicated actions, and set the semantic value of YYS.
 *  If result != yyok, the chain of semantic options in YYS has been
 *  cleared instead or it has been left unmodified except that
 *  redundant options may have been removed.  Regardless of whether
 *  result = yyok, YYS has been left with consistent data so that
 *  yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveValue (yyGLRState* yys, yyGLRStack* yystackp, yy::parser& yyparser)
{
  yySemanticOption* yyoptionList = yys->yysemantics.yyfirstVal;
  yySemanticOption* yybest = yyoptionList;
  yySemanticOption** yypp;
  yybool yymerge = yyfalse;
  YYSTYPE yysval;
  YYRESULTTAG yyflag;

  for (yypp = &yyoptionList->yynext; *yypp != YY_NULLPTR; )
    {
      yySemanticOption* yyp = *yypp;

      if (yyidenticalOptions (yybest, yyp))
        {
          yymergeOptionSets (yybest, yyp);
          *yypp = yyp->yynext;
        }
      else
        {
          switch (yypreference (yybest, yyp))
            {
            case 0:
              return yyreportAmbiguity (yybest, yyp, yyparser);
              break;
            case 1:
              yymerge = yytrue;
              break;
            case 2:
              break;
            case 3:
              yybest = yyp;
              yymerge = yyfalse;
              break;
            default:
              /* This cannot happen so it is not worth a YYASSERT (yyfalse),
                 but some compilers complain if the default case is
                 omitted.  */
              break;
            }
          yypp = &yyp->yynext;
        }
    }

  if (yymerge)
    {
      yySemanticOption* yyp;
      int yyprec = yydprec[yybest->yyrule];
      yyflag = yyresolveAction (yybest, yystackp, &yysval, yyparser);
      if (yyflag == yyok)
        for (yyp = yybest->yynext; yyp != YY_NULLPTR; yyp = yyp->yynext)
          {
            if (yyprec == yydprec[yyp->yyrule])
              {
                YYSTYPE yysval_other;
                yyflag = yyresolveAction (yyp, yystackp, &yysval_other, yyparser);
                if (yyflag != yyok)
                  {
                    yydestruct ("Cleanup: discarding incompletely merged value for",
                                yystos[yys->yylrState],
                                &yysval, yyparser);
                    break;
                  }
                yyuserMerge (yymerger[yyp->yyrule], &yysval, &yysval_other);
              }
          }
    }
  else
    yyflag = yyresolveAction (yybest, yystackp, &yysval, yyparser);

  if (yyflag == yyok)
    {
      yys->yyresolved = yytrue;
      yys->yysemantics.yysval = yysval;
    }
  else
    yys->yysemantics.yyfirstVal = YY_NULLPTR;
  return yyflag;
}

static YYRESULTTAG
yyresolveStack (yyGLRStack* yystackp, yy::parser& yyparser)
{
  if (yystackp->yysplitPoint != YY_NULLPTR)
    {
      yyGLRState* yys;
      int yyn;

      for (yyn = 0, yys = yystackp->yytops.yystates[0];
           yys != yystackp->yysplitPoint;
           yys = yys->yypred, yyn += 1)
        continue;
      YYCHK (yyresolveStates (yystackp->yytops.yystates[0], yyn, yystackp
                             , yyparser));
    }
  return yyok;
}

static void
yycompressStack (yyGLRStack* yystackp)
{
  yyGLRState* yyp, *yyq, *yyr;

  if (yystackp->yytops.yysize != 1 || yystackp->yysplitPoint == YY_NULLPTR)
    return;

  for (yyp = yystackp->yytops.yystates[0], yyq = yyp->yypred, yyr = YY_NULLPTR;
       yyp != yystackp->yysplitPoint;
       yyr = yyp, yyp = yyq, yyq = yyp->yypred)
    yyp->yypred = yyr;

  yystackp->yyspaceLeft += yystackp->yynextFree - yystackp->yyitems;
  yystackp->yynextFree = ((yyGLRStackItem*) yystackp->yysplitPoint) + 1;
  yystackp->yyspaceLeft -= yystackp->yynextFree - yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;

  while (yyr != YY_NULLPTR)
    {
      yystackp->yynextFree->yystate = *yyr;
      yyr = yyr->yypred;
      yystackp->yynextFree->yystate.yypred = &yystackp->yynextFree[-1].yystate;
      yystackp->yytops.yystates[0] = &yystackp->yynextFree->yystate;
      yystackp->yynextFree += 1;
      yystackp->yyspaceLeft -= 1;
    }
}

static YYRESULTTAG
yyprocessOneStack (yyGLRStack* yystackp, size_t yyk,
                   size_t yyposn, yy::parser& yyparser)
{
  while (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    {
      yyStateNum yystate = yystackp->yytops.yystates[yyk]->yylrState;
      YYDPRINTF ((stderr, "Stack %lu Entering state %d\n",
                  (unsigned long int) yyk, yystate));

      YYASSERT (yystate != YYFINAL);

      if (yyisDefaultedState (yystate))
        {
          YYRESULTTAG yyflag;
          yyRuleNum yyrule = yydefaultAction (yystate);
          if (yyrule == 0)
            {
              YYDPRINTF ((stderr, "Stack %lu dies.\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          yyflag = yyglrReduce (yystackp, yyk, yyrule, yyimmediate[yyrule], yyparser);
          if (yyflag == yyerr)
            {
              YYDPRINTF ((stderr,
                          "Stack %lu dies "
                          "(predicate failure or explicit user error).\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          if (yyflag != yyok)
            return yyflag;
        }
      else
        {
          yySymbol yytoken;
          int yyaction;
          const short int* yyconflicts;

          yystackp->yytops.yylookaheadNeeds[yyk] = yytrue;
          if (yychar == YYEMPTY)
            {
              YYDPRINTF ((stderr, "Reading a token: "));
              yychar = yylex (&yylval);
            }

          if (yychar <= YYEOF)
            {
              yychar = yytoken = YYEOF;
              YYDPRINTF ((stderr, "Now at end of input.\n"));
            }
          else
            {
              yytoken = YYTRANSLATE (yychar);
              YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
            }

          yygetLRActions (yystate, yytoken, &yyaction, &yyconflicts);

          while (*yyconflicts != 0)
            {
              YYRESULTTAG yyflag;
              size_t yynewStack = yysplitStack (yystackp, yyk);
              YYDPRINTF ((stderr, "Splitting off stack %lu from %lu.\n",
                          (unsigned long int) yynewStack,
                          (unsigned long int) yyk));
              yyflag = yyglrReduce (yystackp, yynewStack,
                                    *yyconflicts,
                                    yyimmediate[*yyconflicts], yyparser);
              if (yyflag == yyok)
                YYCHK (yyprocessOneStack (yystackp, yynewStack,
                                          yyposn, yyparser));
              else if (yyflag == yyerr)
                {
                  YYDPRINTF ((stderr, "Stack %lu dies.\n",
                              (unsigned long int) yynewStack));
                  yymarkStackDeleted (yystackp, yynewStack);
                }
              else
                return yyflag;
              yyconflicts += 1;
            }

          if (yyisShiftAction (yyaction))
            break;
          else if (yyisErrorAction (yyaction))
            {
              YYDPRINTF ((stderr, "Stack %lu dies.\n",
                          (unsigned long int) yyk));
              yymarkStackDeleted (yystackp, yyk);
              break;
            }
          else
            {
              YYRESULTTAG yyflag = yyglrReduce (yystackp, yyk, -yyaction,
                                                yyimmediate[-yyaction], yyparser);
              if (yyflag == yyerr)
                {
                  YYDPRINTF ((stderr,
                              "Stack %lu dies "
                              "(predicate failure or explicit user error).\n",
                              (unsigned long int) yyk));
                  yymarkStackDeleted (yystackp, yyk);
                  break;
                }
              else if (yyflag != yyok)
                return yyflag;
            }
        }
    }
  return yyok;
}

static void
yyreportSyntaxError (yyGLRStack* yystackp, yy::parser& yyparser)
{
  if (yystackp->yyerrState != 0)
    return;
#if ! YYERROR_VERBOSE
  yyerror (yyparser, YY_("syntax error"));
#else
  {
  yySymbol yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);
  size_t yysize0 = yytnamerr (YY_NULLPTR, yytokenName (yytoken));
  size_t yysize = yysize0;
  yybool yysize_overflow = yyfalse;
  char* yymsg = YY_NULLPTR;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected").  */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[yystackp->yytops.yystates[0]->yylrState];
      yyarg[yycount++] = yytokenName (yytoken);
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for this
             state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;
          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytokenName (yyx);
                {
                  size_t yysz = yysize + yytnamerr (YY_NULLPTR, yytokenName (yyx));
                  yysize_overflow |= yysz < yysize;
                  yysize = yysz;
                }
              }
        }
    }

  switch (yycount)
    {
#define YYCASE_(N, S)                   \
      case N:                           \
        yyformat = S;                   \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  {
    size_t yysz = yysize + strlen (yyformat);
    yysize_overflow |= yysz < yysize;
    yysize = yysz;
  }

  if (!yysize_overflow)
    yymsg = (char *) YYMALLOC (yysize);

  if (yymsg)
    {
      char *yyp = yymsg;
      int yyi = 0;
      while ((*yyp = *yyformat))
        {
          if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
            {
              yyp += yytnamerr (yyp, yyarg[yyi++]);
              yyformat += 2;
            }
          else
            {
              yyp++;
              yyformat++;
            }
        }
      yyerror (yyparser, yymsg);
      YYFREE (yymsg);
    }
  else
    {
      yyerror (yyparser, YY_("syntax error"));
      yyMemoryExhausted (yystackp);
    }
  }
#endif /* YYERROR_VERBOSE */
  yynerrs += 1;
}

/* Recover from a syntax error on *YYSTACKP, assuming that *YYSTACKP->YYTOKENP,
   yylval, and yylloc are the syntactic category, semantic value, and location
   of the lookahead.  */
static void
yyrecoverSyntaxError (yyGLRStack* yystackp, yy::parser& yyparser)
{
  size_t yyk;
  int yyj;

  if (yystackp->yyerrState == 3)
    /* We just shifted the error token and (perhaps) took some
       reductions.  Skip tokens until we can proceed.  */
    while (yytrue)
      {
        yySymbol yytoken;
        if (yychar == YYEOF)
          yyFail (yystackp, yyparser, YY_NULLPTR);
        if (yychar != YYEMPTY)
          {
            yytoken = YYTRANSLATE (yychar);
            yydestruct ("Error: discarding",
                        yytoken, &yylval, yyparser);
          }
        YYDPRINTF ((stderr, "Reading a token: "));
        yychar = yylex (&yylval);
        if (yychar <= YYEOF)
          {
            yychar = yytoken = YYEOF;
            YYDPRINTF ((stderr, "Now at end of input.\n"));
          }
        else
          {
            yytoken = YYTRANSLATE (yychar);
            YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
          }
        yyj = yypact[yystackp->yytops.yystates[0]->yylrState];
        if (yypact_value_is_default (yyj))
          return;
        yyj += yytoken;
        if (yyj < 0 || YYLAST < yyj || yycheck[yyj] != yytoken)
          {
            if (yydefact[yystackp->yytops.yystates[0]->yylrState] != 0)
              return;
          }
        else if (! yytable_value_is_error (yytable[yyj]))
          return;
      }

  /* Reduce to one stack.  */
  for (yyk = 0; yyk < yystackp->yytops.yysize; yyk += 1)
    if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
      break;
  if (yyk >= yystackp->yytops.yysize)
    yyFail (yystackp, yyparser, YY_NULLPTR);
  for (yyk += 1; yyk < yystackp->yytops.yysize; yyk += 1)
    yymarkStackDeleted (yystackp, yyk);
  yyremoveDeletes (yystackp);
  yycompressStack (yystackp);

  /* Now pop stack until we find a state that shifts the error token.  */
  yystackp->yyerrState = 3;
  while (yystackp->yytops.yystates[0] != YY_NULLPTR)
    {
      yyGLRState *yys = yystackp->yytops.yystates[0];
      yyj = yypact[yys->yylrState];
      if (! yypact_value_is_default (yyj))
        {
          yyj += YYTERROR;
          if (0 <= yyj && yyj <= YYLAST && yycheck[yyj] == YYTERROR
              && yyisShiftAction (yytable[yyj]))
            {
              /* Shift the error token.  */
              YY_SYMBOL_PRINT ("Shifting", yystos[yytable[yyj]],
                               &yylval, &yyerrloc);
              yyglrShift (yystackp, 0, yytable[yyj],
                          yys->yyposn, &yylval);
              yys = yystackp->yytops.yystates[0];
              break;
            }
        }
      if (yys->yypred != YY_NULLPTR)
        yydestroyGLRState ("Error: popping", yys, yyparser);
      yystackp->yytops.yystates[0] = yys->yypred;
      yystackp->yynextFree -= 1;
      yystackp->yyspaceLeft += 1;
    }
  if (yystackp->yytops.yystates[0] == YY_NULLPTR)
    yyFail (yystackp, yyparser, YY_NULLPTR);
}

#define YYCHK1(YYE)                                                          \
  do {                                                                       \
    switch (YYE) {                                                           \
    case yyok:                                                               \
      break;                                                                 \
    case yyabort:                                                            \
      goto yyabortlab;                                                       \
    case yyaccept:                                                           \
      goto yyacceptlab;                                                      \
    case yyerr:                                                              \
      goto yyuser_error;                                                     \
    default:                                                                 \
      goto yybuglab;                                                         \
    }                                                                        \
  } while (0)

/*----------.
| yyparse.  |
`----------*/

int
yyparse (yy::parser& yyparser)
{
  int yyresult;
  yyGLRStack yystack;
  yyGLRStack* const yystackp = &yystack;
  size_t yyposn;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY;
  yylval = yyval_default;

  if (! yyinitGLRStack (yystackp, YYINITDEPTH))
    goto yyexhaustedlab;
  switch (YYSETJMP (yystack.yyexception_buffer))
    {
    case 0: break;
    case 1: goto yyabortlab;
    case 2: goto yyexhaustedlab;
    default: goto yybuglab;
    }
  yyglrShift (&yystack, 0, 0, 0, &yylval);
  yyposn = 0;

  while (yytrue)
    {
      /* For efficiency, we have two loops, the first of which is
         specialized to deterministic operation (single stack, no
         potential ambiguity).  */
      /* Standard mode */
      while (yytrue)
        {
          yyRuleNum yyrule;
          int yyaction;
          const short int* yyconflicts;

          yyStateNum yystate = yystack.yytops.yystates[0]->yylrState;
          YYDPRINTF ((stderr, "Entering state %d\n", yystate));
          if (yystate == YYFINAL)
            goto yyacceptlab;
          if (yyisDefaultedState (yystate))
            {
              yyrule = yydefaultAction (yystate);
              if (yyrule == 0)
                {

                  yyreportSyntaxError (&yystack, yyparser);
                  goto yyuser_error;
                }
              YYCHK1 (yyglrReduce (&yystack, 0, yyrule, yytrue, yyparser));
            }
          else
            {
              yySymbol yytoken;
              if (yychar == YYEMPTY)
                {
                  YYDPRINTF ((stderr, "Reading a token: "));
                  yychar = yylex (&yylval);
                }

              if (yychar <= YYEOF)
                {
                  yychar = yytoken = YYEOF;
                  YYDPRINTF ((stderr, "Now at end of input.\n"));
                }
              else
                {
                  yytoken = YYTRANSLATE (yychar);
                  YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
                }

              yygetLRActions (yystate, yytoken, &yyaction, &yyconflicts);
              if (*yyconflicts != 0)
                break;
              if (yyisShiftAction (yyaction))
                {
                  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
                  yychar = YYEMPTY;
                  yyposn += 1;
                  yyglrShift (&yystack, 0, yyaction, yyposn, &yylval);
                  if (0 < yystack.yyerrState)
                    yystack.yyerrState -= 1;
                }
              else if (yyisErrorAction (yyaction))
                {

                  yyreportSyntaxError (&yystack, yyparser);
                  goto yyuser_error;
                }
              else
                YYCHK1 (yyglrReduce (&yystack, 0, -yyaction, yytrue, yyparser));
            }
        }

      while (yytrue)
        {
          yySymbol yytoken_to_shift;
          size_t yys;

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            yystackp->yytops.yylookaheadNeeds[yys] = yychar != YYEMPTY;

          /* yyprocessOneStack returns one of three things:

              - An error flag.  If the caller is yyprocessOneStack, it
                immediately returns as well.  When the caller is finally
                yyparse, it jumps to an error label via YYCHK1.

              - yyok, but yyprocessOneStack has invoked yymarkStackDeleted
                (&yystack, yys), which sets the top state of yys to NULL.  Thus,
                yyparse's following invocation of yyremoveDeletes will remove
                the stack.

              - yyok, when ready to shift a token.

             Except in the first case, yyparse will invoke yyremoveDeletes and
             then shift the next token onto all remaining stacks.  This
             synchronization of the shift (that is, after all preceding
             reductions on all stacks) helps prevent double destructor calls
             on yylval in the event of memory exhaustion.  */

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            YYCHK1 (yyprocessOneStack (&yystack, yys, yyposn, yyparser));
          yyremoveDeletes (&yystack);
          if (yystack.yytops.yysize == 0)
            {
              yyundeleteLastStack (&yystack);
              if (yystack.yytops.yysize == 0)
                yyFail (&yystack, yyparser, YY_("syntax error"));
              YYCHK1 (yyresolveStack (&yystack, yyparser));
              YYDPRINTF ((stderr, "Returning to deterministic operation.\n"));

              yyreportSyntaxError (&yystack, yyparser);
              goto yyuser_error;
            }

          /* If any yyglrShift call fails, it will fail after shifting.  Thus,
             a copy of yylval will already be on stack 0 in the event of a
             failure in the following loop.  Thus, yychar is set to YYEMPTY
             before the loop to make sure the user destructor for yylval isn't
             called twice.  */
          yytoken_to_shift = YYTRANSLATE (yychar);
          yychar = YYEMPTY;
          yyposn += 1;
          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            {
              int yyaction;
              const short int* yyconflicts;
              yyStateNum yystate = yystack.yytops.yystates[yys]->yylrState;
              yygetLRActions (yystate, yytoken_to_shift, &yyaction,
                              &yyconflicts);
              /* Note that yyconflicts were handled by yyprocessOneStack.  */
              YYDPRINTF ((stderr, "On stack %lu, ", (unsigned long int) yys));
              YY_SYMBOL_PRINT ("shifting", yytoken_to_shift, &yylval, &yylloc);
              yyglrShift (&yystack, yys, yyaction, yyposn,
                          &yylval);
              YYDPRINTF ((stderr, "Stack %lu now in state #%d\n",
                          (unsigned long int) yys,
                          yystack.yytops.yystates[yys]->yylrState));
            }

          if (yystack.yytops.yysize == 1)
            {
              YYCHK1 (yyresolveStack (&yystack, yyparser));
              YYDPRINTF ((stderr, "Returning to deterministic operation.\n"));
              yycompressStack (&yystack);
              break;
            }
        }
      continue;
    yyuser_error:
      yyrecoverSyntaxError (&yystack, yyparser);
      yyposn = yystack.yytops.yystates[0]->yyposn;
    }

 yyacceptlab:
  yyresult = 0;
  goto yyreturn;

 yybuglab:
  YYASSERT (yyfalse);
  goto yyabortlab;

 yyabortlab:
  yyresult = 1;
  goto yyreturn;

 yyexhaustedlab:
  yyerror (yyparser, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturn;

 yyreturn:
  if (yychar != YYEMPTY)
    yydestruct ("Cleanup: discarding lookahead",
                YYTRANSLATE (yychar), &yylval, yyparser);

  /* If the stack is well-formed, pop the stack until it is empty,
     destroying its entries as we go.  But free the stack regardless
     of whether it is well-formed.  */
  if (yystack.yyitems)
    {
      yyGLRState** yystates = yystack.yytops.yystates;
      if (yystates)
        {
          size_t yysize = yystack.yytops.yysize;
          size_t yyk;
          for (yyk = 0; yyk < yysize; yyk += 1)
            if (yystates[yyk])
              {
                while (yystates[yyk])
                  {
                    yyGLRState *yys = yystates[yyk];
                  if (yys->yypred != YY_NULLPTR)
                      yydestroyGLRState ("Cleanup: popping", yys, yyparser);
                    yystates[yyk] = yys->yypred;
                    yystack.yynextFree -= 1;
                    yystack.yyspaceLeft += 1;
                  }
                break;
              }
        }
      yyfreeGLRStack (&yystack);
    }

  return yyresult;
}

/* DEBUGGING ONLY */
#if YYDEBUG
static void
yy_yypstack (yyGLRState* yys)
{
  if (yys->yypred)
    {
      yy_yypstack (yys->yypred);
      YYFPRINTF (stderr, " -> ");
    }
  YYFPRINTF (stderr, "%d@%lu", yys->yylrState,
             (unsigned long int) yys->yyposn);
}

static void
yypstates (yyGLRState* yyst)
{
  if (yyst == YY_NULLPTR)
    YYFPRINTF (stderr, "<null>");
  else
    yy_yypstack (yyst);
  YYFPRINTF (stderr, "\n");
}

static void
yypstack (yyGLRStack* yystackp, size_t yyk)
{
  yypstates (yystackp->yytops.yystates[yyk]);
}

#define YYINDEX(YYX)                                                         \
    ((YYX) == YY_NULLPTR ? -1 : (yyGLRStackItem*) (YYX) - yystackp->yyitems)


static void
yypdumpstack (yyGLRStack* yystackp)
{
  yyGLRStackItem* yyp;
  size_t yyi;
  for (yyp = yystackp->yyitems; yyp < yystackp->yynextFree; yyp += 1)
    {
      YYFPRINTF (stderr, "%3lu. ",
                 (unsigned long int) (yyp - yystackp->yyitems));
      if (*(yybool *) yyp)
        {
          YYASSERT (yyp->yystate.yyisState);
          YYASSERT (yyp->yyoption.yyisState);
          YYFPRINTF (stderr, "Res: %d, LR State: %d, posn: %lu, pred: %ld",
                     yyp->yystate.yyresolved, yyp->yystate.yylrState,
                     (unsigned long int) yyp->yystate.yyposn,
                     (long int) YYINDEX (yyp->yystate.yypred));
          if (! yyp->yystate.yyresolved)
            YYFPRINTF (stderr, ", firstVal: %ld",
                       (long int) YYINDEX (yyp->yystate
                                             .yysemantics.yyfirstVal));
        }
      else
        {
          YYASSERT (!yyp->yystate.yyisState);
          YYASSERT (!yyp->yyoption.yyisState);
          YYFPRINTF (stderr, "Option. rule: %d, state: %ld, next: %ld",
                     yyp->yyoption.yyrule - 1,
                     (long int) YYINDEX (yyp->yyoption.yystate),
                     (long int) YYINDEX (yyp->yyoption.yynext));
        }
      YYFPRINTF (stderr, "\n");
    }
  YYFPRINTF (stderr, "Tops:");
  for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
    YYFPRINTF (stderr, "%lu: %ld; ", (unsigned long int) yyi,
               (long int) YYINDEX (yystackp->yytops.yystates[yyi]));
  YYFPRINTF (stderr, "\n");
}
#endif

#undef yylval
#undef yychar
#undef yynerrs



#line 454 "src/syntax.y" // glr.c:2584


/* location parser error
void yy::parser::error(const location& loc, const string& msg){
    ante::error(msg.c_str(), yylexer->fileName, yylexer->getRow(), yylexer->getCol());
} */

void yy::parser::error(const string& msg){
    ante::error(msg.c_str(), yylexer->fileName, yylexer->getRow(), yylexer->getCol());
}

#endif
#line 4300 "src/parser.cpp" // glr.c:2584

/*------------------.
| Report an error.  |
`------------------*/

static void
yyerror (yy::parser& yyparser, const char* msg)
{
  YYUSE (yyparser);
  yyparser.error (msg);
}



namespace yy {
#line 4316 "src/parser.cpp" // glr.c:2584
  /// Build a parser object.
  parser::parser ()
#if YYDEBUG
     :yycdebug_ (&std::cerr)
#endif
  {
  }

  parser::~parser ()
  {
  }

  int
  parser::parse ()
  {
    return ::yyparse (*this);
  }

#if YYDEBUG
  /*--------------------.
  | Print this symbol.  |
  `--------------------*/

  inline void
  parser::yy_symbol_value_print_ (int yytype,
                           const semantic_type* yyvaluep)
  {
    YYUSE (yyvaluep);
    std::ostream& yyoutput = debug_stream ();
    std::ostream& yyo = yyoutput;
    YYUSE (yyo);
    YYUSE (yytype);
  }


  void
  parser::yy_symbol_print_ (int yytype,
                           const semantic_type* yyvaluep)
  {
    *yycdebug_ << (yytype < YYNTOKENS ? "token" : "nterm")
               << ' ' << yytname[yytype] << " (";
    yy_symbol_value_print_ (yytype, yyvaluep);
    *yycdebug_ << ')';
  }

  std::ostream&
  parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  parser::debug_level_type
  parser::debug_level () const
  {
    return yydebug;
  }

  void
  parser::set_debug_level (debug_level_type l)
  {
    // Actually, it is yydebug which is really used.
    yydebug = l;
  }

#endif

} // yy
#line 4391 "src/parser.cpp" // glr.c:2584
