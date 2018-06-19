#include "rpc.h"

#include <stdlib.h>
#include <string.h>

//@ #include "quantifiers.gh"

#define SERVER_PORT 121212

void client(char *key, int key_len, char *request, char *response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?client, _) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?creator, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 bad(creator) ||
                 request(creator, shared_with(creator, id), req_cs) == true &*&
               chars(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(client, _) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 col || bad(creator) || bad(shared_with(creator, id)) ||
                 response(creator, shared_with(creator, id),
                          req_cs, resp_cs); @*/
{
  //@ open principal(client, _);
  int socket;
  char hmac[64];

  net_usleep(20000);
  if(net_connect(&socket, NULL, SERVER_PORT) != 0)
    abort();
  if(net_set_block(socket) != 0)
    abort();

  {
    int message_len = 1 + PACKAGE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();

    *message = '0';
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    memcpy(message + 1, request, PACKAGE_SIZE);
    //@ list<char> t_req_cs = cons('0', req_cs);
    //@ assert chars(message, PACKAGE_SIZE + 1, t_req_cs);
    //@ chars_to_crypto_chars(message, PACKAGE_SIZE + 1);
    sha512_hmac(key, (unsigned int) key_len, message,
                (unsigned int) PACKAGE_SIZE + 1, hmac, 0);
    //@ assert cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ close rpc_pub(hmac_cg);
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
    //@ chars_to_crypto_chars(hmac, 64);
    memcpy(message + PACKAGE_SIZE + 1, hmac, 64);
    //@ crypto_chars_to_chars(hmac, 64);
    //@ chars_to_crypto_chars(message + 1 + 40, 64);
    //@ crypto_chars_join(message);
    net_send(&socket, message, (unsigned int) message_len);
    free(message);
  }

  {
    int size;
    char request2[PACKAGE_SIZE];
    char buffer[MAX_MESSAGE_SIZE];
    size = net_recv(&socket, buffer, MAX_MESSAGE_SIZE);
    int expected_size = 1 + 2 * PACKAGE_SIZE + 64;
    if (size != expected_size) abort();
    //@ chars_split(buffer, expected_size);
    /*@ close hide_chars((void*) buffer + expected_size,
                         MAX_MESSAGE_SIZE - expected_size, _); @*/

    //Verify the hmac
    //@ assert chars(buffer, 1 + 2 * PACKAGE_SIZE, ?cont_cs);
    //@ chars_to_crypto_chars(buffer, 1 + 2 * PACKAGE_SIZE);
    sha512_hmac(key, (unsigned int) key_len, buffer,
                (unsigned int) (1 + 2 * PACKAGE_SIZE), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ close memcmp_secret(hmac, 64, hmac_cs, hmac_cg);
    //@ assert hmac_cg == cg_hmac(creator, id, cont_cs);
    //@ chars_to_crypto_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
    if (memcmp((void*) buffer + 1 + 2 * PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ assert chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs);
    //@ public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
    //@ public_crypto_chars(hmac, 64);
    //@ crypto_chars_to_chars((void*) buffer, 1 + 2 * PACKAGE_SIZE);
    //@ assert chars(buffer, expected_size, append(cont_cs, hmac_cs));

    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '1') abort();
    //Check if response is for the correct request
    //@ chars_split((void*) buffer + 1, PACKAGE_SIZE);
    //@ chars_to_crypto_chars((void*) buffer + 1, PACKAGE_SIZE);
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    if (memcmp(request, (void*) buffer + 1, PACKAGE_SIZE) != 0) abort();

    //Retrieve the actual response
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE);
    memcpy(response, (void*) buffer + 1 + PACKAGE_SIZE, PACKAGE_SIZE);
    //@ assert chars(response, PACKAGE_SIZE, ?resp_cs);

    /*@ if (!col && !bad(creator) && !bad(shared_with(creator, id)))
        {
          switch (cont_cs)
          {
            case cons(c1, cs1):
              if (c1 == '1')
              {
                public_chars((void*) buffer + 1 + 2 * PACKAGE_SIZE, 64);
                public_chars_extract(hmac, hmac_cg);
                open [_]rpc_pub(hmac_cg);
              }
              else
              {
                assert false;
              }
            case nil:
              assert false;
          };

          assert true ==
                   response(creator, shared_with(creator, id), req_cs, resp_cs);
        }
    @*/

    /*@ open hide_chars((void*) buffer + expected_size,
                        MAX_MESSAGE_SIZE - expected_size, _); @*/
    //@ crypto_chars_join((void*) buffer + 1);
    //@ crypto_chars_to_chars((void*) buffer + 1, 2 * PACKAGE_SIZE);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    //@ chars_join(buffer);
    //@ assert chars(buffer, MAX_MESSAGE_SIZE, _);
  }
  net_close(socket);
  //@ close principal(client, _);
}

// This function represents the server application.
// We pass the key predicate just to get hold of the creator principal id.
void compute_response(char* request, char* response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, ?count) &*&
               [?f1]cryptogram(?key, ?key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
               [?f2]chars(request, PACKAGE_SIZE, ?req_cs) &*&
               chars(response, PACKAGE_SIZE, _) &*&
               (
                 col || bad(client) || bad(server) ||
                 request(client, server, req_cs)
               ); @*/
  /*@ ensures  principal(server, count + 1) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               [f2]chars(request, PACKAGE_SIZE, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
               true == response(client, server, req_cs, resp_cs); @*/
{
  //@ open principal(server, count);
  havege_state havege_state;
  //@ close havege_state(&havege_state);
  havege_init(&havege_state);

  //@ close random_request(server, 0, false);
  if (havege_random(&havege_state, response, PACKAGE_SIZE) != 0) abort();

  //@ assert cryptogram(response, PACKAGE_SIZE, ?resp_cs, ?resp_cg);
  //@ close rpc_pub(resp_cg);
  //@ leak rpc_pub(resp_cg);
  //@ public_cryptogram(response, resp_cg);
  //@ assume (response(client, server, req_cs, resp_cs));

  havege_free(&havege_state);
  //@ open havege_state(&havege_state);
  //@ close principal(server, count + 1);
}

void server(char *key, int key_len, char *request, char *response)
  /*@ requires [_]public_invar(rpc_pub) &*&
               principal(?server, _) &*&
               [?f1]cryptogram(key, key_len, ?key_cs, ?key_cg) &*&
                 key_cg == cg_symmetric_key(?client, ?id) &*&
                 server == shared_with(client, id) &*&
               chars(request, PACKAGE_SIZE, _) &*&
               chars(response, PACKAGE_SIZE, _); @*/
  /*@ ensures  principal(server, _) &*&
               [f1]cryptogram(key, key_len, key_cs, key_cg) &*&
               chars(request, PACKAGE_SIZE, ?req_cs) &*&
                 col || bad(client) ||
                 request(client, server, req_cs) &*&
               chars(response, PACKAGE_SIZE, ?resp_cs) &*&
                 col || bad(client) || bad(server) ||
                 response(client, server, req_cs, resp_cs); @*/
{
  //@ open principal(server, _);
  int socket1;
  int socket2;

  if(net_bind(&socket1, NULL, SERVER_PORT) != 0)
    abort();
  if(net_accept(socket1, &socket2, NULL) != 0)
    abort();
  if(net_set_block(socket2) != 0)
    abort();

  {
    int size;
    char buffer[MAX_MESSAGE_SIZE];
    char hmac[64];

    size = net_recv(&socket2, buffer, MAX_MESSAGE_SIZE);
    int expected_size = 1 + PACKAGE_SIZE + 64;
    if (size != expected_size) abort();
    //@ chars_split(buffer, expected_size);
    /*@ close hide_chars((void*) buffer + expected_size,
                         MAX_MESSAGE_SIZE - expected_size, _); @*/

    //Verify the hmac
    //@ chars_to_crypto_chars(buffer, 1 + PACKAGE_SIZE);
    sha512_hmac(key, (unsigned int) key_len, buffer,
                (unsigned int) (1 + PACKAGE_SIZE), hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(client, id, ?cont_cs);
    //@ public_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ close memcmp_secret(hmac, 64, hmac_cs, hmac_cg);
    if (memcmp((void*) buffer + 1 + PACKAGE_SIZE, hmac, 64) != 0) abort();
    //@ public_crypto_chars(hmac, 64);
    //@ crypto_chars_join(buffer);
    //@ crypto_chars_to_chars(buffer, expected_size);
    //@ assert chars(buffer, expected_size, append(cont_cs, hmac_cs));

    //Check the message tag hmac
    //@ chars_split(buffer, 1);
    if (buffer[0] != '0') abort();
    //Retrieve the actual request
    //@ chars_to_crypto_chars((void*) buffer + 1, PACKAGE_SIZE);
    memcpy(request, (void*) buffer + 1, PACKAGE_SIZE);
    //@ assert chars(request, PACKAGE_SIZE, ?req_cs);
    /*@ switch (cont_cs)
        {
          case cons(c1, cs1):
            assert cont_cs == cons('0', req_cs);
            if (!col && c1 == '0' && !bad(client))
            {
              public_chars_extract((void*) buffer + 1 + PACKAGE_SIZE, hmac_cg);
              open [_]rpc_pub(hmac_cg);
              assert (true == request(client, server, req_cs));
            }
          case nil:
            assert false;
        }
    @*/
    //@ chars_to_crypto_chars((void*) buffer + 1 + PACKAGE_SIZE, 64);
    //@ crypto_chars_join((void*) buffer + 1);
    //@ crypto_chars_to_chars((void*) buffer + 1, PACKAGE_SIZE + 64);
    //@ chars_join(buffer);
    /*@ open hide_chars((void*) buffer + expected_size,
                        MAX_MESSAGE_SIZE - expected_size, _); @*/
  }

  //@ assert chars(request, PACKAGE_SIZE, ?req_cs);
  //@ close principal(server, _);
  compute_response(request, response);
  //@ open principal(server, _);
  //@ assert chars(response, PACKAGE_SIZE, ?resp_cs);

  {
    char hmac[64];

    int message_len = 1 + 2 * PACKAGE_SIZE + 64;
    char* message = malloc(message_len);
    if (message == 0) abort();
    //@ chars_split(message, 1 + 2 * PACKAGE_SIZE);

    //@ chars_split(message, 1);
    *message = '1';
    //@ open chars(message + 1, 0, _);
    //@ chars_split(message + 1, PACKAGE_SIZE);
    //@ chars_to_crypto_chars(request, PACKAGE_SIZE);
    memcpy(message + 1, request, PACKAGE_SIZE);
    //@ chars_to_crypto_chars(response, PACKAGE_SIZE);
    memcpy(message + 1 + PACKAGE_SIZE, response, PACKAGE_SIZE);
    //@ crypto_chars_join(message + 1);
    //@ crypto_chars_to_chars(message + 1, 2 * PACKAGE_SIZE);
    //@ close chars(message, 1, _);
    //@ chars_join(message);
    //@ list<char> pay = cons('1', append(req_cs, resp_cs));
    //@ assert chars(message, 1 + 2 * PACKAGE_SIZE, pay);

    //@ chars_to_crypto_chars(message, 1 + 2 * PACKAGE_SIZE);
    sha512_hmac(key, (unsigned int) key_len, message,
                (unsigned int) 2 * PACKAGE_SIZE + 1, hmac, 0);
    //@ open cryptogram(hmac, 64, ?hmac_cs, ?hmac_cg);
    //@ assert hmac_cg == cg_hmac(client, id, pay);
    memcpy(message + 1 + 2 * PACKAGE_SIZE, hmac, 64);
    //@ close cryptogram(message + 1 + 2 * PACKAGE_SIZE, 64, hmac_cs, hmac_cg);
    //@ drop_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ take_append(PACKAGE_SIZE, req_cs, resp_cs);
    //@ close rpc_pub(hmac_cg);
    //@ leak rpc_pub(hmac_cg);
    //@ public_cryptogram(message + 1 + 2 * PACKAGE_SIZE, hmac_cg);
    //@ crypto_chars_to_chars(message, 1 + 2 * PACKAGE_SIZE);
    //@ assert chars(message, message_len, _);

    net_send(&socket2, message, (unsigned int) message_len);
    free((void*) message);
    //@ close cryptogram(hmac, 64, hmac_cs, hmac_cg);
    //@ public_cryptogram(hmac, hmac_cg);
  }

  net_close(socket2);
  net_close(socket1);
  //@ close principal(server, _);
}
