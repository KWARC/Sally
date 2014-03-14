var mockdata = {
    "bookName": "SimplePricing.xlsx",
    "sheets": [
        {
            "sheetName": "Vendor",
            "sheetData": [
                {
                    "idx": "1",
                    "name": "Price",
                    "range": "A4:A11",
                    "meaning": "gaggadaf"
                },
                {
                    "idx": "2",
                    "name": "ice",
                    "range": "A4:A12",
                    "meaning": "blahblah"
                },
                {
                    "idx": "3",
                    "name": "rice",
                    "range": "A4:A13",
                    "meaning": "blahblahasdfasdfasdfasdfhadfsdfaasdfadfafasdfasdfasdfaeesradsfs"
                }
            ]
        },
        {
            "sheetName": "Customer",
            "sheetData": [
                {
                    "idx": "1",
                    "name": "CustomerA",
                    "range": "A3:A9",
                    "meaning": "Price per piece"
                },
                {
                    "idx": "2",
                    "name": "Price",
                    "range": "A4:A11",
                    "meaning": "blahblah"
                },
                {
                    "idx": "3",
                    "name": "CustomerA",
                    "range": "A3:A9",
                    "meaning": "Price per piece"
                }
            ]
        }
    ]
};



/**
TODO fix this module pattern
*/
// var Current = (function() {
//     var sheetNum = 0;
//     var inRelations = 0;

//     return {
//         setSheetNum: function(num) {
//             console.log("Sheetnum updated")
//             sheetNum = num; 
//         },
//         getSheetNum: function() {
//             return sheetNum; 
//         }
//     };

// })();




  $( document ).ready(init);
 
  function getBookName(){
    return mockdata.bookName;
  }

  function getSheetNames(){
    var sheetnames = [];
    for (var i in mockdata.sheets){
      sheetnames[i] = mockdata.sheets[i].sheetName;
    }
    return sheetnames;
  }

  
  function init(){
    console.log(getBookName(), getSheetNames());
    
    //fill forms
    fillTreeSideBar();
    fillBlocksTable();
    
    //events
    document.getElementById("addblocksrow").onclick = addRow;
    document.getElementById("semundo").onclick = semUndo;
    document.getElementById("semredo").onclick = semRedo;
    document.getElementById("nsemundo").onclick = nsemUndo;
    document.getElementById("nsemredo").onclick = nsemRedo;
    document.getElementById("checkall").onchange = checkAll;
    document.getElementById("deleteblocksrows").onclick = deleteRows;
    document.getElementById("semauto").onclick = semAuto;


    //listen for any form updates and modify json accordingly. n.b. in memory save does not validate form data
    listenForInputs();

    //Persist form's data in a browser's Local Storage and never loose them on occasional tabs closing, browser crashes and other disasters
    $('#basic_form').sisyphus({
      timeout: 10
    });

  }
  var sheetNum = 0;
  var inRelations = 0;
  var latestJSID = 0;
  var undoManager = new UndoManager();

  function setSheetNum(num) {
    console.log("Sheetnum updated: "+num)
    sheetNum = num; 
  }
  function getSheetNum() {
    console.log(sheetNum)
    return sheetNum; 
  }
  function setJSID(num) {
    console.log("JSID updated: "+num)
    latestJSID = num; 
  }
  function getJSID() {
    console.log(latestJSID)
    return latestJSID; 
  }

  function addRow(){

    addBlocksItem();

    // make undo-able
    undoManager.add({
        undo: function() {
          console.log("Trying to removeBlocksItem")
          unAddBlocksItem();
        },
        redo: function() {
          console.log("Trying to addBlocksItem")
          addBlocksItem();
        }
    });
  }

  // function delRows(){
  //   deleteRows();

  //   undoManager.add({
  //     undo: function(){

  //   },
  //   redo: function(){

  //   }
  //   });
  // }



function semUndo(){
  document.execCommand('undo', false, null);
}

function semRedo(){
  document.execCommand('redo', false, null);
}

function nsemUndo(){
  undoManager.undo();
}

function nsemRedo(){
  undoManager.redo();
}

function semAuto(){
  fillBlocksTable(0,mockdata); //or any other jsonObject 
}

function checkAll() {
     var checkboxes = new Array();
     checkboxes = document.getElementsByTagName('input'); 
     for (var i = 0; i < checkboxes.length; i++) {
         if (checkboxes[i].type == 'checkbox') {
             checkboxes[i].setAttribute('checked', true)
         }
     }
 }



//Helper Utilities can be put in another file
function setAttributes(el, attrs) {
  for(var key in attrs) {
    el.setAttribute(key, attrs[key]);
  }
  return el;
}

  function listenForInputs(){
    $('#todo-list').on(
      "change", ".new-concept,.new-range,.new-meaning", function() {
        var jsid = $(this).closest("tr").attr('id');
        var classArray = $(this).closest("input").attr('class').split(/\s+/);
        var newVal =  $(this).closest("input").val();
        console.log("Current Sheet: "+ getSheetNum()+" jsid: "+jsid+" classArray: "+classArray+" newVal: "+newVal);
        console.log("updating after one second");
        setTimeout(function() {
          updateJSON(jsid, classArray, newVal, getSheetNum());
        }, 1000);
      }
    );
  }

  function updateJSON(jsid, classArray, newVal, currentSheetNum){
    
    if (jQuery.inArray("new-concept",classArray) !==-1){
      console.log("inArray concept");
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        console.log("inFor "+mockdata.sheets[currentSheetNum].sheetData.length+" "+mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx);
        if (mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx == jsid) {
          console.log("inJsid "+jsid+" vs "+mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx);
          mockdata.sheets[currentSheetNum].sheetData[jsid-1].name = newVal;
          console.log("JSON name updated"+mockdata.sheets[currentSheetNum].sheetData[jsid-1].name);
          break;
        }
      }
    }
    else if (jQuery.inArray("new-range",classArray) !==-1){
      console.log("inArray range");
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        console.log("inFor "+mockdata.sheets[currentSheetNum].sheetData.length+" "+mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx);
        if (mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx == jsid) {
          mockdata.sheets[currentSheetNum].sheetData[jsid-1].range = newVal;
          console.log("JSON range updated"+mockdata.sheets[currentSheetNum].sheetData[jsid-1].range);
          break;
        }
      }
    }
    else if (jQuery.inArray("new-meaning",classArray) !==-1){
      console.log("inArray meaning");
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        if (mockdata.sheets[currentSheetNum].sheetData[jsid-1].idx == jsid) {
          mockdata.sheets[currentSheetNum].sheetData[jsid-1].meaning = newVal;
          console.log("JSON meaning updated"+mockdata.sheets[currentSheetNum].sheetData[jsid-1].meaning);
          break;
        }
      }
    }
    else{
      console.log("Cannot recognize the input type yet.")
    }
  }

  function fillTreeSideBar(){
    var sheetNames = getSheetNames();
    var temptree = "<ul><li><span><a onclick = fillBlocksTable()>"+getBookName()+"</a><\/span><ul>";
    console.log(temptree);
    for (var i in sheetNames){
      temptree = temptree + "<li><span><a onclick = fillBlocksTable("+ i +")>"+sheetNames[i]+"</a><\/span><\/li>"; 
    console.log(temptree);
    }
    temptree = temptree + "<\/ul><\/li><\/ul>";
    var htmltree = $.parseHTML(temptree);

    $("#sheetTree").append(htmltree);
  }

  function fillBlocksTable(num,autodata){
    $("#todo-list").empty();

    var temprow = "{{#sheetData}}<tr id={{idx}}><td><input type=\"checkbox\"><\/td><td><input type=\"text\" value={{name}} class=\"span12 new-concept\"><\/td><td><input type=\"text\" value={{range}} class=\"new-range span12\"><\/td><td><span class=\"span16 uri new-meaning\" type=\"text\">{{meaning}}<\/span><\/td><\/tr>{{/sheetData}}";
    
    if (num == null){
      num = 0;
    }
    if (autodata != null){
      mockdata = autodata;
    } 
    
    var htmlrow = $.parseHTML(Mustache.render(temprow, mockdata.sheets[num]));
    setSheetNum(num);
    
    $("#todo-list").append(htmlrow);
  }

  function fillRelationsTable(num){

  }

  //adds current length + 1 as the id of the new json node and appends a new blank row to the form
  function addBlocksItem(){
    var newID = mockdata.sheets[getSheetNum()].sheetData.length+1;
    var temprow = "<tr id="+ newID +"><td><input type=\"checkbox\"><\/td><td><input type=\"text\" placeholder=\"Bolt 1\" class=\"span12 new-concept\"><\/td><td><input type=\"text\" placeholder=\"sheet!A3:B6\" class=\"new-range span12\"><\/td><td><span class=\"span16 uri new-meaning\" type=\"text\">URI<\/td><\/tr>"
    var htmlrow = $.parseHTML(temprow);
    $("#todo-list").append(htmlrow);
    console.log("newID:"+newID);
    currentSheetNum = getSheetNum();
    addObject = {};
    mockdata.sheets[currentSheetNum].sheetData.push(addObject); 
    mockdata.sheets[currentSheetNum].sheetData[newID-1].idx = newID;
    mockdata.sheets[currentSheetNum].sheetData[newID-1].name = "";
    mockdata.sheets[currentSheetNum].sheetData[newID-1].range = "";
    mockdata.sheets[currentSheetNum].sheetData[newID-1].meaning = "URI";
    setJSID(newID);
  }

  function unAddBlocksItem(){
    var newID = getJSID();
    unAddRowByID(newID);
    mockdata.sheets[getSheetNum()].sheetData.splice(newID, 1);
    setJSID(newID-1);
  }

 function deleteRows() {
     try {
         var table = document.getElementById("blockstable");
         var rowCount = table.rows.length;

         for (var i = 1; i < rowCount; i++) {
            var row = table.rows[i];
            var chkbox = row.cells[0].childNodes[0];
            if (null != chkbox && true == chkbox.checked) {
                table.deleteRow(i);
                // $(chkbox).closest("tr").remove();
                rowCount--;
                i--;
              }
            }
        }
      catch (e) {
         console.log(e);
     }
 }

  function unAddRowByID(delID) {
     try {
         var table = document.getElementById("blockstable");
         var rowCount = table.rows.length;

         for (var i = 1; i < rowCount; i++) {
            var row = table.rows[i];
            var chkbox = row.cells[0].childNodes[0];

            if (i === delID){
                table.deleteRow(i);
                console.log("Removed id: " +i);
                rowCount--;
                i--;                
              }
            }
          
        }
     catch (e) {
         console.log(e);
     }
 }


