#include <malloc.h>
#include <string.h>
#include <stdio.h>
#include "stringBuffersExt.h"
#include "sockets0.h"

void socket_write_string(struct socket *socket, char *string)
{
    struct writer *writer = socket_get_writer(socket);
    writer_write_string(writer, string);
}

void socket_write_string_literal(struct socket *socket, char *stringLiteral)
{
    socket_write_string(socket, stringLiteral);
}

void socket_write_integer(struct socket *socket, int value)
{
    char buffer[20];
    sprintf(buffer, "%d", value);
    socket_write_string(socket, buffer);
}

char *socket_read_line(struct socket *socket, int maxLength)
{
    struct reader *reader = socket_get_reader(socket);
    struct string_buffer *buffer = create_string_buffer();
    bool result = reader_read_line(reader, buffer);
    if (result) {
        string_buffer_dispose(buffer);
        return 0;
    } else {
        char *cs = string_buffer_get_chars(buffer);
        int length = string_buffer_get_length(buffer);
        if (length > maxLength)
            length = maxLength;
        char *dup = malloc(length + 1);
        memcpy(dup, cs, length);
        dup[length] = 0;
        string_buffer_dispose(buffer);
        return dup;
    }
}
