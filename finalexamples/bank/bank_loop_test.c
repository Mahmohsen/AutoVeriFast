//#include "bool.h"
#include "malloc.h"
#include "strings.h"
#include "stdlib.h"
#include "sockets.h"




//The following predicates are auto generated 
/*@ 

predicate authenticate_result (struct authenticate_result *authenticate_result;) = 
authenticate_result->user_account |-> ?user_account &*& authenticate_result->is_teller |-> ?is_teller &*& authenticate_result->real_name |-> ?real_name &*& string1(real_name) &*& malloc_block_authenticate_result(authenticate_result) ; 

predicate transaction (struct transaction *transaction; int count) = 
 transaction == 0 ? count == 0 : transaction->next |-> ?next &*& transaction->counterparty_bank_account_id |-> ?counterparty_bank_account_id &*& string1(counterparty_bank_account_id) &*& transaction->amount |-> ?amount &*& transaction->comment |-> ?comment &*&  string1(comment)&*& malloc_block_transaction(transaction)  &*& transaction(next, ?count1) &*& count == count1 + 1; 

predicate bank_account (struct bank_account *bank_account; int count) = 
 bank_account == 0 ? count == 0 : bank_account->next |-> ?next &*& bank_account->id |-> ?id &*& string1(id) &*& bank_account->owner |-> ?owner &*& bank_account->balance |-> ?balance &*& bank_account->transaction_count |-> ?transaction_count &*&  bank_account->transactions |-> ?transactions &*& transaction(transactions, transaction_count) &*& malloc_block_bank_account(bank_account)  &*& bank_account(next, ?count1) &*& count == count1 + 1; 

predicate user_account (struct user_account *user_account; int count) = 
 user_account == 0 ? count == 0 : user_account->next |-> ?next &*& user_account->user_name |-> ?user_name &*& string1(user_name) &*& user_account->password |-> ?password &*& string1(password) &*& user_account->is_teller |-> ?is_teller &*& user_account->real_name |-> ?real_name &*& string1(real_name) &*& malloc_block_user_account(user_account)  &*& user_account(next, ?count1) &*& count == count1 + 1; 

predicate bank (struct bank *bank; int user_count, int bank_count ) = 
bank->user_account_count |-> ?user_account_count &*& bank->user_accounts |-> ?user_accounts &*& bank->bank_account_count |-> ?bank_account_count &*& bank->bank_accounts |-> ?bank_accounts &*& malloc_block_bank(bank) &*& user_account(user_accounts, user_count)&*& user_count == user_account_count &*& bank_account(bank_accounts, bank_count) &*& bank_count == bank_account_count; 

//predicate socket (struct socket *socket;) = 
//socket->iden |-> ?iden &*& malloc_block_socket(socket) ; 
@*/





//@autogen bank = Many user_account
//@autogen bank = Many bank_account
 


struct socket { int iden;};


struct bank {
    int user_account_count;
    struct user_account *user_accounts;
    int bank_account_count;
    struct bank_account *bank_accounts;
};

struct user_account {
    struct user_account *next;
    char *user_name;
    char *password;
    int is_teller;
    char *real_name;
};

struct bank_account {
    struct bank_account *next;
    char *id;
    struct user_account *owner;
    int balance;
    int transaction_count;
    struct transaction *transactions;
};

struct transaction {
    struct transaction *next;
    char *counterparty_bank_account_id;
    int amount;
    char *comment;
};

char *string_copy(char *string)
//@requires true &*& string1(string);
//@ensures true &*& string1(result) &*& string1(string);
{
    char *copy = strdup(string);
    if (copy == 0) {
        abort();
    }
    return copy;
}

bool register_transaction(struct socket *socket, struct bank_account *bankAccounts, char *fromId, char *toId, int amount, char *comment, struct user_account *originator)
//@ requires true &*& socket(socket) &*& string1(fromId) &*& bank_account(bankAccounts,?count0) &*& string1(toId) &*& string1(comment);
//@ ensures true &*& socket(socket) &*& string1(fromId) &*& bank_account(bankAccounts,count0) &*& string1(toId) &*& string1(comment);
{
    if (bankAccounts == 0) {
        socket_write_string(socket, fromId);
        socket_write_string_literal(socket, ": No such bank account.\r\n");
        return false;
    } else {
    	
        int cmp = strcmp(bankAccounts->id, fromId);
        if (cmp == 0) {
            if (amount < 0 && bankAccounts->owner != originator) {
                socket_write_string_literal(socket, "You do not own this account.\r\n");
                return false;
            } else {
                if (bankAccounts->balance + amount < 0) {
                    socket_write_string_literal(socket, "You have insufficient funds available on this account.\r\n");
                    return false;
                } else {
                    struct transaction *transaction = malloc(sizeof(struct transaction));
                    if (transaction == 0) {
                        abort();
                    }
                    int txCount = bankAccounts->transaction_count;
                    bankAccounts->transaction_count = txCount + 1;
                    transaction->next = bankAccounts->transactions;
                    char *toIdCopy = string_copy(toId);
                    transaction->counterparty_bank_account_id = toIdCopy;
                    transaction->amount = amount;
                    char *commentCopy = string_copy(comment);
                    transaction->comment = commentCopy;
                    bankAccounts->transactions = transaction;
                    bankAccounts->balance = bankAccounts->balance + amount;
                    return true;
                }
            }
        } else {
            bool result = register_transaction(socket, bankAccounts->next, fromId, toId, amount, comment, originator);
            return result;
        }
    }
}

void socket_write_transactions_helper2(struct socket *socket, int count, struct transaction *transactions)
//@ requires true &*& transaction(transactions,?count1) &*& count1 == count &*& socket(socket);
//@ ensures true &*& transaction(transactions,count) &*& socket(socket);
{
    if (0 < count) {  
//@open transaction(transactions,count1); 
        if (transactions->amount < 0) {
            socket_write_string_literal(socket, "Transfer of ");
            socket_write_integer(socket, 0 - transactions->amount);
            socket_write_string_literal(socket, " to ");
            socket_write_string(socket, transactions->counterparty_bank_account_id);
            socket_write_string_literal(socket, " with comment ");
            socket_write_string(socket, transactions->comment);
            socket_write_string_literal(socket, "\r\n");
        } else {
            socket_write_string_literal(socket, "Transfer of ");
            socket_write_integer(socket, transactions->amount);
            socket_write_string_literal(socket, " from ");
            socket_write_string(socket, transactions->counterparty_bank_account_id);
            socket_write_string_literal(socket, " with comment ");
            socket_write_string(socket, transactions->comment);
            socket_write_string_literal(socket, "\r\n");
        }
        socket_write_transactions_helper2(socket, count - 1, transactions->next);
    }
}

void socket_write_transactions_helper(struct socket *socket, int index, struct bank_account *bankAccounts, struct user_account *userAccount)
//@ requires true &*& bank_account(bankAccounts,?count0) &*& socket(socket);
//@ ensures true &*& bank_account(bankAccounts,count0) &*& socket(socket);
{
    if (bankAccounts != 0) {
        if (bankAccounts->owner == userAccount) {
            if (index == 0) {
                socket_write_transactions_helper2(socket, bankAccounts->transaction_count, bankAccounts->transactions);
            } else {
                socket_write_transactions_helper(socket, index - 1, bankAccounts->next, userAccount);
            }
        } else {
            socket_write_transactions_helper(socket, index, bankAccounts->next, userAccount);
        }
    }
}

void socket_write_bank_accounts_helper(struct socket *socket, int i, int count, struct bank_account *bankAccounts, struct user_account *userAccount)
//@ requires true &*& bank_account(bankAccounts,?count1) &*& count1 == count &*& socket(socket);
//@ ensures true &*& bank_account(bankAccounts,count) &*& socket(socket);
{
    if (0 < count) {
//@open bank_account(bankAccounts,count1); 
        if (bankAccounts->owner == userAccount) {
            socket_write_integer(socket, i);
            socket_write_string_literal(socket, ". Id: ");
            socket_write_string(socket, bankAccounts->id);
            socket_write_string_literal(socket, "; Balance: ");
            socket_write_integer(socket, bankAccounts->balance);
            socket_write_string_literal(socket, ".\r\n");
            socket_write_bank_accounts_helper(socket, i + 1, count - 1, bankAccounts->next, userAccount);
        } else {
            socket_write_bank_accounts_helper(socket, i, count - 1, bankAccounts->next, userAccount);
        }
    }
}

struct user_account *lookup_user_account(int count, struct user_account *userAccounts, char *userName)
//@ requires true &*& user_account(userAccounts,?count1) &*& count1 == count &*& string1(userName);
//@ ensures true &*& user_account(userAccounts,count1) &*& string1(userName);
{
    if (count == 0) {
        return 0;
    } else {
//@open user_account(userAccounts,count1); 
        int cmp = strcmp(userAccounts->user_name, userName);
        if (cmp == 0) {
            return userAccounts;
        } else {
            struct user_account *account = lookup_user_account(count - 1, userAccounts->next, userName);
    	    return account;
        }
    }
}

struct authenticate_result 
{
    struct user_account *user_account;
    int is_teller;
    char *real_name;
};

struct authenticate_result *authenticate_user(struct user_account *userAccounts, char *userName, char *password)
//@ requires true &*& user_account(userAccounts,?count0) &*& string1(userName) &*& string1(password);
//@ ensures true &*& string1(userName) &*& string1(password) &*& user_account(userAccounts,count0) &*& (result==0 ? true: authenticate_result(result));
{
    if (userAccounts == 0) {
        return 0;
    } else {
        int userAccountCmp = strcmp(userAccounts->user_name, userName);
        if (userAccountCmp == 0) {
            int passwordCmp = strcmp(userAccounts->password, password);
            if (passwordCmp == 0) {
                struct authenticate_result *result = malloc(sizeof(struct authenticate_result));
                if (result == 0) {
                    abort();
                }
                result->user_account = userAccounts;
                result->is_teller = userAccounts->is_teller;
                char *realNameCopy = string_copy(userAccounts->real_name);
                result->real_name = realNameCopy;
                return result;
            } else {
                return 0;
            }
        } else {
            struct authenticate_result *result = authenticate_user(userAccounts->next, userName, password);
            return result;
        }
    }
}

int socket_read_nonneg_integer_helper(struct socket *socket)
//@ requires true &*& socket(socket);
//@ ensures true &*& socket(socket);
{
    char *buffer = socket_read_line(socket, 20);
    if (buffer == 0) {
        return -1;
    } else {
        int value = parse_nonneg_integer(buffer);
        string_dispose(buffer);
        return value;
    }
}

// Add code below this line

// Add code above this line

void handle_connection(struct bank *bank, struct socket *socket, struct user_account *userAccount, int isTeller, char *realName)
//@ requires true &*& socket(socket) &*& string1(realName) &*& bank->user_account_count |-> ?_userAccountCount &*& bank->user_accounts |-> ?userAccounts &*& user_account(userAccounts, _userAccountCount) &*& bank->bank_account_count |-> ?_bankAccountCount &*& bank->bank_accounts |-> ?bankAccounts &*& bank_account(bankAccounts, _bankAccountCount);
//@ ensures true &*& bank->user_account_count |-> ?_userAccountCount2 &*& bank->user_accounts |-> ?_userAccounts2 &*& user_account(_userAccounts2, _userAccountCount2) &*& bank->bank_account_count |-> ?_bankAccountCount2 &*& bank->bank_accounts |-> ?_bankAccounts2 &*& bank_account(_bankAccounts2, _bankAccountCount2) &*& socket(socket) &*& string1(realName);

{
    socket_write_string_literal(socket, "Welcome, ");
    socket_write_string(socket, realName);
    socket_write_string_literal(socket, ".\r\n");
    bool done = false;
    while (!done)
        //    /*@ invariant
        //        bank->user_account_count |-> ?_userAccountCount0 &*& bank->user_accounts |-> ?_userAccounts0 &*& user_account(_userAccounts0, _userAccountCount0)
        //        &*& bank->bank_account_count |-> ?_bankAccountCount0 &*& bank->bank_accounts |-> ?_bankAccounts0 &*& bank_account(_bankAccounts0, _bankAccountCount0)
        //        &*& socket(socket);
       //  @*/
       /*@ 
       		requires socket(socket) &*& bank_user_accounts(bank,?_userAccounts) &*& bank_user_account_count(bank,?_userAccountCount0) &*& user_account(_userAccounts,_userAccountCount0) &*&
   	 		bank_bank_accounts(bank,?_bankAccounts) &*& bank_bank_account_count(bank, ?_bankAccountCount0) &*& bank_account(_bankAccounts, _bankAccountCount0);
       @*/
       /*@ 
       		ensures socket(socket) &*& bank_user_accounts(bank,?_userAccounts0) &*& bank_user_account_count(bank,?_userAccountCount1) &*& user_account(_userAccounts0,_userAccountCount1) &*&
   	 		bank_bank_accounts(bank,?_bankAccounts0) &*& bank_bank_account_count(bank, ?_bankAccountCount1) &*& bank_account(_bankAccounts0, _bankAccountCount1);
       @*/
    {
        if (isTeller != 0) {
            socket_write_string_literal(socket, "Teller Menu\r\n1. Add user account\r\n2. Add bank account\r\n3. Close bank account\r\n4. Close user account\r\n0. Done\r\n");
            int choice = socket_read_nonneg_integer_helper(socket);
            if (choice == 1) {
                socket_write_string_literal(socket, "Enter user name for new account:\r\n");
                char *userName = socket_read_line(socket, 30);
                if (userName != 0) {
                    socket_write_string_literal(socket, "Enter password for new account:\r\n");
                    char *password = socket_read_line(socket, 30);
                    if (password != 0) {
                        socket_write_string_literal(socket, "Enter real name for new account:\r\n");
                        char *newAccountRealName = socket_read_line(socket, 30);
                        if (newAccountRealName != 0) {
                            struct user_account *newAccount = malloc(sizeof(struct user_account));
                            if (newAccount == 0) {
                                abort();
                            }
                            newAccount->user_name = userName;
                            newAccount->password = password;
                            newAccount->is_teller = 0;
                            newAccount->real_name = newAccountRealName;
                            newAccount->next = bank->user_accounts;
                            bank->user_accounts = newAccount;
                            bank->user_account_count = bank->user_account_count + 1;
                            socket_write_string_literal(socket, "The new user account has been added.\r\n");
                        } else {
                            string_dispose(password);
                            string_dispose(userName);
                            done = true;
                        }
                    } else {
                        string_dispose(userName);
                        done = true;
                    }
                } else {
                    done = true;
                }
            } else {
                if (choice == 2) {
                    socket_write_string_literal(socket, "Please enter an ID for the new account.\r\n");
                    char *id = socket_read_line(socket, 20);
                    if (id != 0) {
                        socket_write_string_literal(socket, "Please enter the user name of the owner of the new account.\r\n");
                        char *ownerUserName = socket_read_line(socket, 30);
                        if (ownerUserName != 0) {
                            struct user_account *ownerAccount = lookup_user_account(bank->user_account_count, bank->user_accounts, ownerUserName);
                            string_dispose(ownerUserName);
                            if (ownerAccount == 0) {
                                socket_write_string_literal(socket, "No such user.\r\n");
                                string_dispose(id);
                            } else {
                                socket_write_string_literal(socket, "Please enter the amount of the initial deposit.\r\n");
                                int amount = socket_read_nonneg_integer_helper(socket);
                                if (amount < 0) {
                                    string_dispose(id);
                                    done = true;
                                } else {
                                    struct bank_account *account = malloc(sizeof(struct bank_account));
                                    if (account == 0) {
                                        abort();
                                    }
                                    account->next = bank->bank_accounts;
                                    account->id = id;
                                    account->owner = ownerAccount;
                                    account->balance = amount;
                                    account->transaction_count = 0;
                                    account->transactions = 0;
                                    bank->bank_accounts = account;
                                    bank->bank_account_count = bank->bank_account_count + 1;
                                    socket_write_string_literal(socket, "The new account has been added.\r\n");
                                }
                            }
                        } else {
                            string_dispose(id);
                            done = true;
                        }
                    } else {
                        done = true;
                    }
                } else {
                    if (choice == 3) {
                        // Add code below this line
                        // Add code above this line
                    } else {
                        if (choice  == 4) {
                            // Add code below this line
                            // Add code above this line
                        } else {
                            done = true;
                        }
                    }
                }
            }
        } else {
            socket_write_string_literal(socket, "Client menu\r\n1. View accounts\r\n2. Perform wire transfer\r\n0. Done\r\n");
            int choice = socket_read_nonneg_integer_helper(socket);
            if (choice == 1) {
                socket_write_string_literal(socket, "Accounts:\r\n");
                socket_write_bank_accounts_helper(socket, 1, bank->bank_account_count, bank->bank_accounts, userAccount);
                socket_write_string_literal(socket, "Enter account index to view transactions:\r\n");
                int index = socket_read_nonneg_integer_helper(socket);
                if (index < 0) {
                    done = true;
                } else {
                    if (1 <= index) {
                        socket_write_transactions_helper(socket, index - 1, bank->bank_accounts, userAccount);
                    }
                }
            } else {
               if (choice == 2) {
                   socket_write_string_literal(socket, "Please enter the account id of your account:\r\n");
                   char *fromId = socket_read_line(socket, 30);
                   if (fromId != 0) {
                       socket_write_string_literal(socket, "Please enter the target account id:\r\n");
                       char *toId = socket_read_line(socket, 30);
                       if (toId != 0) {
                           socket_write_string_literal(socket, "Please enter the amount:\r\n");
                           int amount = socket_read_nonneg_integer_helper(socket);
                           if (0 <= amount) {
                               socket_write_string_literal(socket, "Please enter the comment:\r\n");
                               char *comment = socket_read_line(socket, 100);
                               if (comment != 0) {
                                   bool result = register_transaction(socket, bank->bank_accounts, fromId, toId, 0 - amount, comment, userAccount);
                                   if (result) {
                                       register_transaction(socket, bank->bank_accounts, toId, fromId, amount, comment, 0);
                                   }
                                   string_dispose(comment);
                               } else {
                                   done = true;
                               }
                           } else {
                               done = true;
                           }
                           string_dispose(toId);
                       } else {
                           done = true;
                       }
                       string_dispose(fromId);
                   } else {
                       done = true;
                   }
               } else {
                   done = true;
               }
           }
       }
       
    //@ recursive_call();
   }
   
}

void add_root_account(struct bank *bank)
//@requires true &*& bank(bank,0, ?count0);
//@ensures true &*& bank(bank,1,count0);
{
    char *rootUserName = create_string("root");
    char *rootPassword = create_string("root");
    char *rootRealName = create_string("root");
    struct user_account *rootAccount = malloc(sizeof(struct user_account));
    if (rootAccount == 0) {
        abort();
    }
    rootAccount->next = bank->user_accounts;
    rootAccount->user_name = rootUserName;
    rootAccount->password = rootPassword;
    rootAccount->is_teller = 1;
    rootAccount->real_name = rootRealName;
    bank->user_accounts = rootAccount;
    bank->user_account_count = 1;
}

int main()
//@requires true;
//@ensures true;
{
    struct bank *bank = malloc(sizeof(struct bank));
    if (bank == 0) {
        abort();
    }
    bank->user_account_count = 0;
    bank->user_accounts = 0;
    bank->bank_account_count = 0;
    bank->bank_accounts = 0;

    add_root_account(bank);

    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
    //        /*@ invariant
    //            server_socket(serverSocket)
    //            &*& bank->user_account_count |-> ?_userAccountCount &*& bank->user_accounts |-> ?_userAccounts &*& user_account(_userAccounts, _userAccountCount)
    //            &*& bank->bank_account_count |-> ?_bankAccountCount &*& bank->bank_accounts |-> ?_bankAccounts &*& bank_account(_bankAccounts, _bankAccountCount);
    //    @*/
    //@ requires server_socket(serverSocket) &*& bank_user_accounts(bank,?userAccounts) &*& user_account(userAccounts,?userAccountCount) &*& bank_user_account_count(bank,userAccountCount) &*& bank_bank_accounts(bank,?bankAccounts) &*& bank_account(bankAccounts,?bankAccountCount) &*& bank_bank_account_count(bank,bankAccountCount);
    //@ ensures true;
    {
        struct socket *socket = server_socket_accept(serverSocket);

        socket_write_string_literal(socket, "Welcome to Home Banking.\r\n");
        socket_write_string_literal(socket, "Please enter your username.\r\n");
        char *userName = socket_read_line(socket, 30);
        if (userName != 0) {
            socket_write_string_literal(socket, "Please enter your password.\r\n");
            char *password = socket_read_line(socket, 30);
            if (password != 0) {
                struct authenticate_result *result = authenticate_user(bank->user_accounts, userName, password);
                if (result == 0) {
                    socket_write_string_literal(socket, "Incorrect username, password combination. Closing the connection.\r\n");
                } else {
                    handle_connection(bank, socket, result->user_account, result->is_teller, result->real_name);
                    string_dispose(result->real_name);
                    free(result);
                }
                string_dispose(password);
            }
            string_dispose(userName);
        }

        socket_close(socket);
        //@recursive_call();
    }
}
