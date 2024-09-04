package global_package;

  typedef enum { READY, STARTPARSING, DATAPARSING, INFOPARSING, ENDPARSING, DONE } e_States;

  typedef enum { START, ENDOPTION, INFO, INFOCONTENTS, DATA, DATALEN, DATACONTENTS } e_options;

  typedef struct {
    e_options           optiontype;
    bit unsigned [31:0] position;
    bit unsigned [31:0] contents;
  } st_Field;

  typedef st_Field a_st_Field_5[4:0];

  typedef struct {
    st_Field     startOption;
    st_Field     endOption;
    st_Field     infoOption;
    st_Field     infoOptionContents;
    st_Field     dataOption;
    st_Field     dataOptionLen;
    a_st_Field_5 dataOptionContents;
    bit          hasStart;
    bit          hasInfo;
    bit          hasData;
    bit          hasEnd;
    bit          isEmpty;
    bit          hasError;
  } st_ParsedOptions;

  typedef bit unsigned [31:0] a_unsigned_32_15[14:0];

endpackage
