#ifndef SOCKETS_H
#define SOCKETS_H

#include "bool.h"
#include "strings.h"

struct server_socket;
struct socket;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires true;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket(result);
void socket_close(struct socket *socket);
    //@ requires socket(socket);
    //@ ensures true;
void socket_write_string(struct socket *socket, char *string);
    //@ requires socket(socket) &*& string1(string);
    //@ ensures socket(socket) &*& string1(string);
void socket_write_integer(struct socket *socket, int value);
    //@ requires socket(socket);
    //@ ensures socket(socket);
char *socket_read_line(struct socket *socket, int maxLength);
    //@ requires socket(socket) &*& 0 <= maxLength;
    //@ ensures socket(socket) &*& (result == 0 ? emp : string1(result));

void socket_write_string_literal(struct socket *socket, char *stringLiteral);
    //@ requires socket(socket); //&*& [?f]chars(stringLiteral, ?length, ?cs) &*& mem('\0', cs) == true;
    //@ ensures socket(socket);// &*& [f]chars(stringLiteral, length, cs);

#endif
