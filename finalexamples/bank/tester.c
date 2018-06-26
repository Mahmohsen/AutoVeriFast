#include <stdio.h>
#include "sockets.h"
#include "sockets0.h"

int main(void)
{
    struct socket *socket;
    char command[200];
    int lineno = 0;

    for (;;) {
        lineno++;
        printf("Executing line %d\n", lineno);
        gets(command);
        switch (command[0]) {
            case 'O':
                socket = create_client_socket(12345);
                break;
            case 'C':
                socket_close(socket);
                break;
            case 'S':
                socket_write_string(socket, command + 1);
                socket_write_string(socket, "\r\n");
                break;
            case 'R':
                {
                char *line = socket_read_line(socket, 200);
                if (line == 0) {
                    printf("error on line %d: connection closed\n", lineno);
                    return 1;
                }
                if (strcmp(line, command + 1) != 0) {
                    printf("error on line %d: mismatch\n", lineno);
                    printf("received: '%s'\n", line);
                    printf("expected: '%s'\n", command + 1);
                    return 1;
                }
                break;
                }
            case 'E':
                printf("Test completed successfully.\n");
                return 0;
            default:
                printf("error on line %d: unknown command: '%c'\n", lineno, command[0]);
        }
    }
}
