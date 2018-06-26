#include <stdlib.h>
#include <errno.h>
#include "strings.h"

char *create_string(char *stringLiteral)
{
    return strdup(stringLiteral);
}

int parse_nonneg_integer(char *string)
{
    char *endptr;
    int result;
    errno = 0;
    result = strtol(string, &endptr, 10);
    if (errno != 0 || *string == 0 || *endptr != 0 || result < 0)
        return -1;
    return result;
}

void string_dispose(char *string)
{
    free(string);
}
