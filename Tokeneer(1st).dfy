class Token{

  var fingerprint : int;
  var clearanceLvl : int;
  var valid :bool;

  method Init(fingerprint : int, clearance : int)
  modifies this;
  requires fingerprint != 0;
  requires 1 <= clearance <= 3;
  ensures this.fingerprint == fingerprint;
  ensures this.clearanceLvl == clearance;
  ensures valid == true;
  {
    this.fingerprint := fingerprint;
    this.clearanceLvl := clearance;
    this.valid := true;
  }

  method invalidate()
  modifies this`valid;
  ensures valid == false;
  {
    valid := false;
  }

}

class IdStn{
  var open : bool;
  var securityLvl : int;
  var alarm : bool;

  method Init(init_securityLvl : int)
  modifies this;
  requires 1 <= init_securityLvl <=3;
  ensures securityLvl == init_securityLvl;
  ensures open == false;
  ensures alarm == false;
  {
    securityLvl := init_securityLvl;
    open := false;
    alarm := false;
  }

  method Open(token : Token, fingerprint : int) returns (access : bool)
  modifies token`valid,this`open, this`alarm;
  requires token.valid;
  requires token != null;
  ensures token.valid && token.clearanceLvl >= securityLvl ==> open == true;
  ensures !token.valid ==> alarm == true;
  {
      if(!token.valid)
      {
        token.invalidate();
        alarm := true;
      }
      else if(token.clearanceLvl >= securityLvl)
      {
        open := true;
      }

  }

  method Close()
  modifies this`open;
  ensures open == false;
  {
    open := false;
  }
}

class EnrollmentStn{
  var users : set<int>;
  var length : int;

  method Init()
  modifies this;
  ensures users == {};
  //ensures fresh(users);
  {
    this.users := {};
    this.length := 0;
  }

  method Enroll(fingerprint: int, clearanceLvl : int) returns (token : Token?)
  modifies this, `length;
  requires clearanceLvl == 1 || clearanceLvl == 2 || clearanceLvl == 3;
  requires fingerprint != 0;
  ensures fingerprint !in users ==> length >= 0;
  ensures fingerprint !in users ==> length >= old(length);
  ensures fingerprint !in users ==> fresh(token);
  ensures fingerprint !in users ==> token.valid == true;
  {
      if (fingerprint in users){
        token := null;
      } else {
        token := new Token.Init(fingerprint, clearanceLvl);
        users := users + {fingerprint};
        length := length + 1;
      }
  }

}

class test{

    /*  var enrollmentStn : EnrollmentStn;
        var clearanceLow : IdStn;
        var clearanceMedium : IdStn;
        var clearanceHigh : IdStn;

        method Init(){
          /* Init EnrollmentStation */
          var enrollmentStn := new EnrollmentStn.Init();

          /* Init Doors */
          var clearanceLow := new IdStn.Init(1);
          var clearanceMedium := new IdStn.Init(2);
          var clearanceHigh := new IdStn.Init(3);
        }
    */


   method test_enrollSuccess_TokenEnrolled(){

     /* Init EnrollmentStation */
      var enrollmentStn := new EnrollmentStn.Init();

     /*Low Clearance*/
     var tokenLow := enrollmentStn.Enroll(1,1);

     /*Medium Clearance*/
     var tokenFail := enrollmentStn.Enroll(1,2); //expecting failure
     var tokenMedium := enrollmentStn.Enroll(2,2);

     /*High Clearance*/
     var tokenHigh := enrollmentStn.Enroll(3,3);

     assert tokenLow != null;
     assert tokenLow.fingerprint == 1;
     assert tokenLow.clearanceLvl == 1;
     assert tokenLow.valid;

     assert tokenFail == null;

   }


}