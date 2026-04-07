// Write in Java a recursive descent parser for the grammar below. The grammar is LL(1). Your main file should be called Parse.java, and if P contains a program to be parsed, then:

// java Parse < P

// should print either

// Program parsed successfully

// or

// Parse error

// depending on whether the input program parses correctly.

// The grammar is:

//    S ::= { L } | System.out.println ( E ) ; | if ( E ) S else S | while ( E ) S

//    L ::= S L | ϵ

//    E ::= true | false | ! E

// where {S, L, E} is the set of nonterminal symbols, S is the start symbol,

//     { } System.out.println ( ) ; if else while true false !

// are the terminal symbols, and ϵ denotes the empty string.