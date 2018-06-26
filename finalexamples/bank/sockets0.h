#ifndef SOCKETS0_H
#define SOCKETS0_H

#include "bool.h"
#include "stringBuffers.h"

struct server_socket;
struct socket;
struct reader;
struct writer;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket, struct reader *reader, struct writer *writer);
predicate reader(struct reader *reader);
predicate writer(struct writer *writer);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires emp;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket0(result, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

struct reader *socket_get_reader(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer);
    //@ ensures socket(socket, reader, writer) &*& result == reader;
struct writer *socket_get_writer(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer);
    //@ ensures socket(socket, reader, writer) &*& result == writer;
void socket_close(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
    //@ ensures emp;
    
bool reader_read_line(struct reader *reader, struct string_buffer *buffer);
    //@ requires reader(reader) &*& string_buffer(buffer);
    //@ ensures reader(reader) &*& string_buffer(buffer);
void writer_write_string(struct writer *writer, char *string);
    //@ requires writer(writer) &*& [?f]chars(string, ?cs) &*& chars_contains(cs, 0) == true;
    //@ ensures writer(writer) &*& [f]chars(string, cs);
void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer);
    //@ requires writer(writer) &*& [?f]string_buffer(buffer);
    //@ ensures writer(writer) &*& [f]string_buffer(buffer);

struct socket *create_client_socket(int port);
    //@ requires emp;
    //@ ensures socket(result, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

#endif
