#ifndef CRYPTOLIB_H
#define CRYPTOLIB_H

#include <pthread.h>
#include <stdbool.h>

//@ #include "proof_obligations.gh"
//@ #include "../polarssl/annotated_api/auxiliary_definitions.gh"

///////////////////////////////////////////////////////////////////////////////
// Module stuff ///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//@ require_module cryptolib;

///////////////////////////////////////////////////////////////////////////////
// Principals /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@ 
predicate principal(int p);

predicate principals_created(int p);

predicate generated_values(int principal, int count);

predicate world(predicate(item) pub);

//to classify messages while defining the pub predicate
predicate_ctor message_tag(item i)(int tag) = true;
@*/

struct keypair;

int create_principal(struct keypair** keypair);
  /*@ requires world(?pub) &*&
               pointer(keypair, _) &*&
               principals_created(?count); @*/
  /*@ ensures  world(pub) &*&
               principals_created(result) &*& 
               result == count + 1 &*&
               principal(result) &*& generated_values(result, 1) &*&
               pointer(keypair, ?p_keypair) &*&
               keypair(p_keypair, result, 1, 0, pub); @*/

/*@
lemma void destroy_principal(int count);
  requires principal(count) &*&
           generated_values(count, _);
  ensures  true;
@*/

///////////////////////////////////////////////////////////////////////////////
// Initialization/Finalization ////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void init_crypto_lib();
  /*@ requires module(cryptolib, true) &*&
               proof_obligations(?pub); @*/
  //@ ensures  world(pub) &*& principals_created(0);

void abort_crypto_lib(const char* message);
  //@ requires [?f]string(message, ?cs);
  //@ ensures  false;

void exit_crypto_lib();
  //@ requires world(?pub) &*& principals_created(_);
  //@ ensures  module(cryptolib, false);

/*@
typedef lemma void not_public(predicate(item) pub, item i, int info)();
  requires  [_]pub(i) &*& [_]info_for_item(i, info);
  ensures   false;
@*/

///////////////////////////////////////////////////////////////////////////////
// Item ///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item;

/*@

inductive item =
  | data_item                 (list<char> data)
  | pair_item                 (item first, item second)
  | nonce_item                (int principal, int count, char inc)
  | symmetric_key_item        (int principal, int count)
  | public_key_item           (int principal, int count)
  | private_key_item          (int principal, int count)
  | hash_item                 (option<item> payload)
  | hmac_item                 (int principal, int count, option<item> payload)
  | symmetric_encrypted_item  (int principal, int count, option<item> payload,
                               list<char> entropy)
  | asymmetric_encrypted_item (int principal, int count, option<item> payload,
                               list<char> entropy)
  | asymmetric_signature_item (int principal, int count, option<item> payload,
                               list<char> entropy)
;

predicate item(struct item *item, item i, predicate(item) pub);

predicate info_for_item(item i, int i);

lemma void get_info_for_item(item i);
  requires true;
  ensures  [_]info_for_item(i, ?info);

lemma void info_for_item_is_function(item i, int info1, int info2);
  requires [_]info_for_item(i, info1) &*& 
           [_]info_for_item(i, info2);
  ensures  info1 == info2;
  
fixpoint bool well_formed_item(item i)
{
  switch (i)
  {
    case pair_item(f0, s0):
      return well_formed_item(f0) && well_formed_item(s0);
    case hash_item(pay0): return
      switch (pay0)
      {
        case some(p):
          return well_formed_item(p);
        case none:
          return false;
      };
    case hmac_item(p0, c0, pay0): return
      switch (pay0)
      {
        case some(p):
          return well_formed_item(p);
        case none:
          return false;
      };
    case symmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    case asymmetric_encrypted_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    case asymmetric_signature_item(p0, c0, pay0, ent0): return
      switch (pay0)
      {
        case some(pay1):
           return well_formed_item(pay1);
         case none:
           return false;
      };
    default:
      return true;
  }
}

@*/

void item_free(struct item* item);
  //@ requires item(item, _, _);
  //@ ensures  emp;

struct item* item_clone(struct item* item);
  //@ requires [?f]item(item, ?i, ?pub);
  /*@ ensures  [f]item(item, i, pub) &*& 
               item(result, i, pub) &*& result != 0; @*/

bool item_equals(struct item* item1, struct item* item2);
  /*@ requires [?f1]item(item1, ?i1, ?pub) &*& [?f2]item(item2, ?i2, pub) &*&
               true == well_formed_item(i1); @*/
  /*@ ensures  [f1]item(item1, i1, pub) &*& [f2]item(item2, i2, pub) &*&
               collision_in_run() ? true : result == (i1 == i2); @*/

///////////////////////////////////////////////////////////////////////////////
// Data item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_data(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == data_item(_) : true; @*/

void check_is_data(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == data_item(_);

struct item *create_data_item(char* data, int length);
  /*@ requires [?f]world(?pub) &*&
               chars(data, length, ?cs) &*& length > 0; @*/
  /*@ ensures  [f]world(pub) &*&
               chars(data, length, cs) &*& 
               item(result, data_item(cs), pub); @*/

struct item *create_data_item_from_char(char i);
  //@ requires [?f]world(?pub);
  /*@ ensures  [f]world(pub) &*&
               item(result, data_item(cons(i, nil)), pub); @*/

int item_get_data(struct item *item, char** data);
  /*@ requires item(item, ?i, ?pub) &*& 
               i == data_item(?cs0) &*& pointer(data, _); @*/
  /*@ ensures  item(item, i, pub) &*& pointer(data, ?p) &*&
               chars(p, result, ?cs1) &*& malloc_block(p, result) &*&
               collision_in_run() ? true : cs0 == cs1; @*/

//Only call this function if you expect the item was constructed with
// "create_data_item_from_char". If it receives a different item it will abort;
char item_get_data_as_char(struct item *item);
  //@ requires item(item, ?i, ?pub) &*& i == data_item(?cs0);
  /*@ ensures  item(item, i, pub) &*& 
               collision_in_run() ? true : cs0 == cons(result, nil); @*/

///////////////////////////////////////////////////////////////////////////////
// Pair item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_pair(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == pair_item(_, _) : true; @*/

void check_is_pair(struct item *item);
  //@ requires item(item, ?p, ?pub);
  //@ ensures  item(item, p, pub) &*& p == pair_item(_, _);

struct item *create_pair(struct item *first, struct item *second);
  //@ requires item(first, ?f, ?pub) &*& item(second, ?s, pub);
  /*@ ensures  item(first, f, pub) &*& item(second, s, pub) &*&
               item(result, pair_item(f, s), pub); @*/

struct item *pair_get_first(struct item *pair);
  //@ requires item(pair, ?p, ?pub);
  /*@ ensures  item(pair, p, pub) &*& p == pair_item(?f, ?s) &*& 
               item(result, ?f0, pub) &*&
               collision_in_run() ? true : f == f0; @*/

struct item *pair_get_second(struct item *pair);
  //@ requires item(pair, ?p, ?pub);
  /*@ ensures  item(pair, p, pub) &*& p == pair_item(?f, ?s) &*& 
               item(result, ?s0, pub) &*&
               collision_in_run() ? true : s == s0; @*/

///////////////////////////////////////////////////////////////////////////////
// Nonce item /////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_nonce(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == nonce_item(_, _, _) : true; @*/

void check_is_nonce(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == nonce_item(_, _, _);

//@ predicate nonce_request(int principal, int info) = emp;

struct item *create_nonce();
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count) &*&
               nonce_request(principal, ?info); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?i, pub) &*& [_]info_for_item(i, info) &*&
               i == nonce_item(principal, count + 1, 0); @*/

void increment_nonce(struct item *item);
  /*@ requires item(item, ?i, ?pub) &*& 
               i == nonce_item(?principal, ?count, ?inc0); @*/
  /*@ ensures  item(item, ?i_inc, pub) &*& 
               [_]info_for_item(i, ?info1) &*&
               [_]info_for_item(i_inc, ?info2) &*&
               collision_in_run() ? 
                 true 
               : 
                 i_inc == nonce_item(principal, count, inc0 + 1) &&
                 info1 == info2; @*/

/*@
lemma void info_for_incremented_nonce(item i, int inc1, int inc2);
  requires [_]info_for_item(i, ?info) &*&
           i == nonce_item(?p, ?c, inc1);
  ensures  [_]info_for_item(nonce_item(p, c, inc2), info);
@*/

void random_buffer(char* buffer, int size);
  /*@ requires [?f]world(?pub) &*&
               chars(buffer, size, _) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               chars(buffer, size, _) &*&
               generated_values(principal, count + 1); @*/

int random_int();
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1); @*/

unsigned int random_u_int();
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal, count + 1); @*/

///////////////////////////////////////////////////////////////////////////////
// Hash item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_hash(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == hash_item(_) : true; @*/

void check_is_hash(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == hash_item(_);

struct item *create_hash(struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, pay, pub) &*& item(result, ?hash, pub) &*& 
               collision_in_run() ? 
                 true
               :
                 hash == hash_item(some(pay)); @*/

///////////////////////////////////////////////////////////////////////////////
// Key item ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

//Symmetric keys

bool is_symmetric_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == symmetric_key_item(_, _) : true; @*/

void check_is_symmetric_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == symmetric_key_item(_, _);

//@ predicate key_request(int principal, int info) = emp;

struct item *create_symmetric_key();
  /*@ requires [?f0]world(?pub) &*&
               key_request(?principal, ?info) &*&
               generated_values(principal, ?count); @*/
  /*@ ensures  [f0]world(pub) &*&
               generated_values(principal, count + 1) &*&
               item(result, ?k, pub) &*&
               k == symmetric_key_item(principal, count + 1) &*&
               [_]info_for_item(k, info); @*/

//Asymmetric keys

bool is_public_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == public_key_item(_, _) : true; @*/

void check_is_public_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == public_key_item(_, _);

bool is_private_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == private_key_item(_, _) : true; @*/

void check_is_private_key(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures item(item, i, pub) &*& i == private_key_item(_, _);

/*@ 

predicate keypair(struct keypair *keypair, int principal, int id, int info,
                  predicate(item) pub);

predicate keypair_request(int principal, int info) = emp;

@*/

struct keypair *create_keypair(int principal);
  /*@ requires world(?pub) &*&
               keypair_request(principal, ?info) &*&
               generated_values(principal, ?count); @*/
  /*@ ensures  world(pub) &*&
               keypair(result, principal, count + 1, info, pub) &*&
               generated_values(principal, count + 1); @*/

void keypair_free(struct keypair *keypair);
  //@ requires keypair(keypair, _, _, _, _);
  //@ ensures  true;

struct item *get_public_key(int participant);
  //@ requires [?f]world(?pub);
  /*@ ensures  [f]world(pub) &*&
               item(result, ?key, pub) &*& 
               key == public_key_item(participant, 1); @*/

/*@
lemma void info_for_asymmetric_keypair(item pub_key, item priv_key);
  requires [_]info_for_item(pub_key, ?info1) &*&
           pub_key == public_key_item(?p, ?c) &*&
           [_]info_for_item(priv_key, ?info2) &*&
           priv_key == private_key_item(p, c);
  ensures  info1 == info2;
@*/

struct item *keypair_get_private_key(struct keypair *keypair);
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == private_key_item(creator, id) &*&
               [_]info_for_item(key, info); @*/

struct item *keypair_get_public_key(struct keypair *keypair);
  //@ requires keypair(keypair, ?creator, ?id, ?info, ?pub);
  /*@ ensures  keypair(keypair, creator, id, info, pub) &*&
               item(result, ?key, pub) &*&
               key == public_key_item(creator, id) &*&
               [_]info_for_item(key, info); @*/

///////////////////////////////////////////////////////////////////////////////
// Hmac item //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_hmac(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == hmac_item(_, _, _) : true; @*/

void check_is_hmac(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == hmac_item(_, _, _);

struct item *create_hmac(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?hmac, pub) &*& 
               collision_in_run() ? 
                 true
               :
                 hmac == hmac_item(principal, count, some(pay)); @*/

void hmac_verify(struct item *hmac, struct item *key, struct item *payload);
/*@ requires [?f]world(?pub) &*&
               item(hmac, ?h, pub) &*& 
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?principal, ?count); @*/
  /*@ ensures  [f]world(pub) &*&
               item(hmac, h, pub) &*& 
               item(payload, pay, pub) &*& item(key, k, pub) &*&
               collision_in_run() ? 
                 true 
               :
                 h == hmac_item(principal, count, some(pay)); @*/

///////////////////////////////////////////////////////////////////////////////
// Symmetric encrypted item ///////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_symmetric_encrypted(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == symmetric_encrypted_item(_, _, _, _) : true; @*/

void check_is_symmetric_encrypted(struct item *item);
  //@ requires item(item, ?i, ?pub);
  //@ ensures  item(item, i, pub) &*& i == symmetric_encrypted_item(_, _, _, _);

/*@
lemma void info_for_symmetric_encrypted_item(item key, item enc);
  requires [_]info_for_item(key, ?info1) &*&
           key == symmetric_key_item(?p, ?c) &*&
           [_]info_for_item(enc, ?info2) &*&
           enc == symmetric_encrypted_item(p, c, _, _);
  ensures  info1 == info2;
@*/

struct item *symmetric_encryption(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?enc, pub) &*& 
               collision_in_run() ?
                 true
               :
                 enc == symmetric_encrypted_item(principal2, count2, 
                                                 some(pay), ?ent); @*/
               
struct item *symmetric_decryption(struct item *key, struct item *item);
  /*@ requires [?f]world(?pub) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
               enc == 
                  symmetric_encrypted_item(?principal1, ?count1, ?pay, ?ent) &*&
               k == symmetric_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*& 
               item(result, ?dec, pub) &*& 
               collision_in_run() ?
                 true
               :
                 count1 == count2 && principal1 == principal2 &&
                 pay == some(dec); @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric encrypted item //////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_asymmetric_encrypted(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == asymmetric_encrypted_item(_, _, _, _) : true; @*/

void check_is_asymmetric_encrypted(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*& 
               i == asymmetric_encrypted_item(_, _, _, _); @*/

/*@
lemma void info_for_asymmetric_encrypted_item(item key, item enc);
  requires [_]info_for_item(key, ?info1) &*&
           key == public_key_item(?p, ?c) &*&
           [_]info_for_item(enc, ?info2) &*&
           enc == asymmetric_encrypted_item(p, c, _, _);
  ensures  info1 == info2;
@*/

struct item *asymmetric_encryption(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == public_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?enc, pub) &*& 
               collision_in_run() ?
                 true
               :
                 enc == asymmetric_encrypted_item(principal2, count2, 
                                                  some(pay), ?ent); @*/
               
struct item *asymmetric_decryption(struct item *key, struct item *item);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(item, ?enc, pub) &*& item(key, ?k, pub) &*&
               enc == 
                  asymmetric_encrypted_item(?principal2, ?count2, ?pay, ?ent) &*&
               k == private_key_item(?principal3, ?count3); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(item, enc, pub) &*& item(key, k, pub) &*& 
               item(result, ?dec, pub) &*& 
               collision_in_run() ? true :
               ( 
                 count2 == count3 && principal2 == principal3 ?
                   pay == some(dec)
                 :
                   [_]pub(dec)
               ); @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric signature item //////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

bool is_asymmetric_signature(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*&
               result ? i == asymmetric_signature_item(_, _, _, _) : true; @*/

void check_is_asymmetric_signature(struct item *item);
  //@ requires item(item, ?i, ?pub);
  /*@ ensures  item(item, i, pub) &*& 
               i == asymmetric_signature_item(_, _, _, _); @*/

/*@
lemma void info_for_asymmetric_signature_item(item key, item enc);
  requires [_]info_for_item(key, ?info1) &*&
           key == private_key_item(?p, ?c) &*&
           [_]info_for_item(enc, ?info2) &*&
           enc == asymmetric_signature_item(p, c, _, _);
  ensures  info1 == info2;
@*/

struct item *asymmetric_signature(struct item *key, struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(payload, ?pay, pub) &*& item(key, ?k, pub) &*& 
               k == private_key_item(?principal2, ?count2); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(payload, pay, pub) &*& item(key, k, pub) &*& 
               item(result, ?sig, pub) &*& 
               collision_in_run() ?
                 true
               :
                 sig == asymmetric_signature_item(principal2, count2, 
                                                  some(pay), ?ent); @*/

void asymmetric_signature_verify(struct item *key, struct item *item, 
                                 struct item *signature);
  /*@ requires [?f]world(?pub) &*&
               item(item, ?i, pub) &*& item(key, ?k, pub) &*&
               item(signature, ?sig, pub) &*&
               k == public_key_item(?principal1, ?count1); @*/
  /*@ ensures  [f]world(pub) &*&
               item(item, i, pub) &*& item(key, k, pub) &*& 
               item(signature, sig, pub) &*& 
               collision_in_run() ? 
                 true 
               :
                 sig == asymmetric_signature_item(principal1, count1, 
                                                  some(i), _); @*/

///////////////////////////////////////////////////////////////////////////////
// Asymmetric authenticated encryption ////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct item *asymmetric_authenticated_encryption(char recipient,
                                                 struct item *public_key,
                                                 struct item *private_key, 
                                                 struct item *payload);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*& 
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*& 
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(payload, ?pay, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 2) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(payload, pay, pub) &*&
               item(result, ?msg, pub) &*& 
               collision_in_run() ?
                 true
               :
                 msg == pair_item(?enc, ?sig) &*&
                 enc == asymmetric_encrypted_item(principal2, count2, 
                                                  some(pay), _) &*&
                 sig == asymmetric_signature_item(principal3, count3, 
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(cons(recipient, nil)), 
                                     hash_item(some(enc))); @*/

struct item *asymmetric_authenticated_decryption(char recipient,
                                                 struct item *public_key,
                                                 struct item *private_key, 
                                                 struct item *message);
  /*@ requires [?f]world(?pub) &*&
               generated_values(?principal1, ?count1) &*&
               item(public_key, ?pub_k, pub) &*& 
                 pub_k == public_key_item(?principal2, ?count2) &*&
               item(private_key, ?priv_k, pub) &*& 
                 priv_k == private_key_item(?principal3, ?count3) &*&
               item(message, ?msg, pub); @*/
  /*@ ensures  [f]world(pub) &*&
               generated_values(principal1, count1 + 1) &*&
               item(public_key, pub_k, pub) &*&
               item(private_key, priv_k, pub) &*&
               item(message, msg, pub) &*&
               item(result, ?decrypted, pub) &*& 
               collision_in_run() ?
                 true
               :
                 msg == pair_item(?enc, ?sig) &*& 
                 enc == asymmetric_encrypted_item(?principal4, ?count4, 
                                                  ?pay, _) &*&
                 sig == asymmetric_signature_item(principal2, count2, 
                                                  some(?msg_id), _) &*&
                 msg_id == pair_item(data_item(cons(recipient, nil)), 
                                     hash_item(some(enc))) &*&
                 principal4 == principal3 && count4 == count3 ?
                   pay == some(decrypted)
                 :
                   [_]pub(decrypted)
               ; @*/

///////////////////////////////////////////////////////////////////////////////
// Network ////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

struct network_status;

//@ predicate network_status(struct network_status *stat);

void network_sleep(unsigned int microseconds);
  //@ requires true;
  //@ ensures  true;

struct network_status *network_connect(const char *name, int port);
  //@ requires [?f1]option_string(name, ?ip);
  //@ ensures  [f1]option_string(name, ip) &*& network_status(result);

struct network_status *network_bind_and_accept(int port);
  //@ requires true;
  //@ ensures  network_status(result);

void network_disconnect(struct network_status *stat);
  //@ requires network_status(stat);
  //@ ensures  true;

void network_send(struct network_status *stat, struct item *datagram);
  /*@ requires [?f]world(?pub) &*&
               network_status(stat) &*&
               item(datagram, ?d, pub) &*& [_]pub(d); @*/
  /*@ ensures  [f]world(pub) &*& network_status(stat) &*&
               item(datagram, d, pub); @*/

struct item *network_receive(struct network_status *stat);
  /*@ requires [?f]world(?pub) &*&
               network_status(stat); @*/
  /*@ ensures  [f]world(pub) &*&
               network_status(stat) &*&
               item(result, ?d, pub) &*& [_]pub(d); @*/

///////////////////////////////////////////////////////////////////////////////
// Proof obligations //////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@

predicate proof_obligations(predicate(item) pub) =
  is_public_collision(_, pub) &*&
  is_public_data(_, pub) &*&
  is_public_pair_compose(_, pub) &*&
  is_public_pair_decompose(_, pub) &*&
  is_public_nonce(_, pub) &*&
  is_public_incremented_nonce(_, pub) &*&
  is_public_hash(_, pub) &*&
  is_public_symmetric_key(_, pub) &*&
  is_public_public_key(_, pub) &*&
  is_public_private_key(_, pub) &*&
  is_public_hmac(_, pub) &*&
  is_public_symmetric_encrypted(_, pub) &*&
  is_public_symmetric_encrypted_entropy(_, pub) &*&
  is_public_symmetric_decrypted(_, pub) &*&
  is_public_asymmetric_encrypted(_, pub) &*&
  is_public_asymmetric_encrypted_entropy(_, pub) &*&
  is_public_asymmetric_decrypted(_, pub) &*&
  is_public_asymmetric_signature(_, pub)
;

typedef lemma void public_collision(predicate(item) pub)(item i);
  requires  true == collision_in_run();
  ensures   [_]pub(i);

typedef lemma void public_data(predicate(item) pub)(item data);
  requires  data == data_item(?d);
  ensures   [_]pub(data);

typedef lemma void public_pair_compose(predicate(item) pub)
                                      (item first, item second);
  requires  [_]pub(first) &*& [_]pub(second);
  ensures   [_]pub(pair_item(first, second));

typedef lemma void public_pair_decompose(predicate(item) pub)(item pair);
  requires  [_]pub(pair_item(?first, ?second));
  ensures   [_]pub(first) &*& [_]pub(second);

typedef lemma void public_nonce(predicate(item) pub)(item nonce);
  requires  nonce == nonce_item(?p, ?c, ?inc) &*& true == bad(p);
  ensures   [_]pub(nonce);
  
typedef lemma void public_incremented_nonce(predicate(item) pub)
                                           (item nonce1, item nonce2);
  requires  nonce1 == nonce_item(?p, ?c, ?inc1) &*&
            nonce2 == nonce_item(p, c, ?inc2) &*&
            [_]pub(nonce1);
  ensures   [_]pub(nonce2);

typedef lemma void public_hash(predicate(item) pub)(item hash);
  requires  hash == hash_item(?pay) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(hash);

typedef lemma void public_symmetric_key(predicate(item) pub)(item key);
  requires  key == symmetric_key_item(?p, _) &*& true == bad(p);
  ensures   [_]pub(key);

typedef lemma void public_public_key(predicate(item) pub)(item key);
  requires  key == public_key_item(_, _);
  ensures   [_]pub(key);

typedef lemma void public_private_key(predicate(item) pub)(item key);
  requires  key == private_key_item(?p, _) &*& true == bad(p);
  ensures   [_]pub(key);

typedef lemma void public_hmac(predicate(item) pub)(item hmac);
  requires  hmac == hmac_item(?p, ?c, ?pay) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(symmetric_key_item(p, c)) &*& 
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(hmac);

typedef lemma void public_symmetric_encrypted(predicate(item) pub)(item enc);
  requires  enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(symmetric_key_item(p, c)) &*& 
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(enc);

typedef lemma void public_symmetric_encrypted_entropy(predicate(item) pub)
                                                     (item enc, list<char> ent);
  requires  [_]pub(enc) &*&
            enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent0);
  ensures   [_]pub(symmetric_encrypted_item(p, c, pay, ent));

typedef lemma void public_symmetric_decrypted(predicate(item) pub)(item enc);
  requires  enc == symmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            [_]pub(enc) &*& [_]pub(symmetric_key_item(p, c));
  ensures   switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };

typedef lemma void public_asymmetric_encrypted(predicate(item) pub)(item enc);
  requires  enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(public_key_item(p, c)) &*& 
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(enc);

typedef lemma void public_asymmetric_encrypted_entropy(predicate(item) pub)
                                                     (item enc, list<char> ent);
  requires  [_]pub(enc) &*&
            enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent0);
  ensures   [_]pub(asymmetric_encrypted_item(p, c, pay, ent));

typedef lemma void public_asymmetric_decrypted(predicate(item) pub)(item enc);
  requires  enc == asymmetric_encrypted_item(?p, ?c, ?pay, ?ent) &*&
            [_]pub(enc) &*& [_]pub(private_key_item(p, c));
  ensures   switch(pay)
            {
              case some(pay0):
                return [_]pub(pay0);
              case none:
                return true;
            };

typedef lemma void public_asymmetric_signature(predicate(item) pub)(item sig);
  requires  sig == asymmetric_signature_item(?p, ?c, ?pay, ?ent) &*&
            switch(pay)
            {
              case some(pay0):
                return [_]pub(private_key_item(p, c)) &*& 
                       [_]pub(pay0);
              case none:
                return true;
            };
  ensures   [_]pub(sig);
@*/

///////////////////////////////////////////////////////////////////////////////
// Attacker ///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

/*@
lemma void retreive_proof_obligations();
  nonghost_callers_only
  requires [?f]world(?pub);
  ensures  [f]world(pub) &*& proof_obligations(pub); 
@*/

void attacker(int attacker_id, struct keypair* keypair);
  /*@ requires [?f]world(?pub) &*&
               true == bad(attacker_id) &*&
               generated_values(attacker_id, ?count) &*&
               keypair(keypair, attacker_id, ?id, ?info, pub) &*&
               principals_created(_); @*/
  //@ ensures false;

///////////////////////////////////////////////////////////////////////////////
// Debugging //////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

void debug_print(const char *message);
  //@ requires [?f]string(message, ?cs);
  //@ ensures  [f]string(message, cs);

void print_buffer(const char *buffer, int size);
  //@ requires [?f]chars(buffer, size, ?cs);
  //@ ensures  [f]chars(buffer, size, cs);

void print_item(const struct item* item);
  //@ requires [?f]item(item, ?i, ?pub);
  //@ ensures  [f]item(item, i, pub);

#endif
