#ifndef STRING_H
#define STRING_H

/*@
predicate string1(char *cl;);
@*/

char *create_string(char *stringLiteral);
    //@ requires [?f]string(stringLiteral, ?cs);
    //@ ensures [f]string(stringLiteral, cs) &*& string1(result);

char *strdup(char *s);
    //@ requires string1(s);
    //@ ensures string1(s) &*& (result == 0 ? true : string1(result));

int strcmp(char *s1, char *s2);
    //@ requires string1(s1) &*& string1(s2);
    //@ ensures string1(s1) &*& string1(s2);

int parse_nonneg_integer(char *string);
    //@ requires string1(string);
    //@ ensures string1(string);

void string_dispose(char *s);
    //@ requires string1(s);
    //@ ensures true;

#endif
