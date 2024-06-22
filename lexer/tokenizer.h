// lexer.h
#include <string>
#include "token.h"
#include <map>

// Declare the global variables used by gettok
extern std::string IdentifierStr; // Filled in if tok_identifier
extern double NumVal;             // Filled in if tok_number
extern int CurTok;

// Declare the gettok function

int GetTokPrecedence(std::map<char, int> *BinopPrecedence);
int getNextToken();