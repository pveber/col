Col -- A syntax extension for easier manipulation of flat records   
=========================================

Scientific data is often stored in the form of tables where each line 
represents an object and columns are descriptors of this object (like in
a spreadsheet). Col is a syntax extension which generates appropriate types 
and functions from a statement describing a flat record, in order to
make the manipulation of this sort of data easier.

Features 
--------

- automatic definition of record, tuple and object types associated to a 
  flat record, as well as conversion functions between them
- generation of serialization functions as tab-separated strings, 
  parsing/unparsing of TSV files.

Authors
---------
This library was written by Martin Jambon ([webpage](http://martin.jambon.free.fr/)) and is currently maintained by Philippe Veber ([github page](https://github.com/pveber)).
