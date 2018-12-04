class Token{
  
  var fingerprint : int;
  var clearanceLvl : int;
  var valid :bool;
  
  method Init(fingerprint : int, clearance : int)
  modifies this;
  {
    this.fingerprint := fingerprint;
    this.clearanceLvl := clearance;
    this.valid := true;
  }
}

class IdStn{
  
  method Init(){
  
  
  }
  
  method Open(user : User, fingerprint : int) returns (access : bool)
  modifies user.token`valid;
  requires validClearance(user.token.valid);
  requires user != null && user.token != null;
  {
  
  }
  
  method Close()
  {
  
  }


}

class EnrollmentStn{

  var users : set<User>;
  method Init()
  modifies this;
  ensures users == {};
  ensures fresh(users);
  {
    this.users := {};
  }
  
  method Enroll(user: User, fingerprint: int, clearanceLvl : int)
  modifies this,user`token, user.token;
  requires user != null && user.token == null;
  requires clearanceLvl == 1 || clearanceLvl == 2 || clearanceLvl == 3;
  requires user !in users ;
  ensures users == old(users) + {user};
  ensures user.token != null;
  ensures user.token.clearanceLvl == clearanceLvl;
  ensures user.token.fingerprint == fingerprint;
  ensures fresh(user);
  ensures user.token.valid == true;
  {
      user.token := new Token.Init(fingerprint, clearanceLvl);
      users := users + {user};
  }

}

class User{
  var token : Token;
 
 method Init()
  modifies this;
  ensures this.token == null;
  {
    this.token := null;
  }
}

method main(){




}
