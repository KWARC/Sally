if not window?
  json = require "./json3"
else
  json = exports.types.json;

class ASMEditor
  constructor: (@snap = {}) ->
    @history = [];

  getSpreadsheets : () ->
    res = [];
    res.push k for k, v of @snap
    res

  getSheets : (spreadsheet) ->
    res = [];
    return res if not @snap[spreadsheet]?
    res.push k for k, v of @snap[spreadsheet]
    res

  getBlocks : (spreadsheet, sheet) ->
    return {} if not @snap[spreadsheet]?
    return {} if not @snap[spreadsheet][sheet]?
    @snap[spreadsheet][sheet]["blocks"]

data = 
  "SimplePricing.xlsx" : 
    "vendor prices" : 
      "blocks" :
        1 :
          name: "bolt",
          range: "vendor!C4:D123"
          meaning: "http://bots.com/bolt.omdoc"

    "customer prices" : 
      "blocks" : [
      ]

if not WEB?
  asm = new ASMEditor(data)
  console.log(asm.getSpreadsheets())
  console.log(asm.getSheets("test.xls"))
  console.log(asm.getBlocks("test.xls", "sheet1"))


if WEB?
  window.asm = data;
  window.ASMEditor = ASMEditor;