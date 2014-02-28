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

var undoManager = new UndoManager();

  function addRow(){

    addBlocksItem();

    // make undo-able
    undoManager.add({
        undo: function() {
            removeBlocksItem();
        },
        redo: function() {
            addBlocksItem();
        }
    });
  }



function semUndo(){
  document.execCommand('undo', false, null);
}

function semRedo(){
  document.execCommand('redo', false, null);
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

var Current = (function() {
    var sheetNum = 0;
    var inRelations = 0;

    return {
        setSheetNum: function(num) {
            console.log("Sheetnum updated")
            sheetNum = num; 
        },
        getSheetNum: function() {
            return sheetNum; 
        }
    };

})();




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
    document.getElementById("addblocksrow").onclick = addBlocksItem;
    document.getElementById("semundo").onclick = semUndo;
    document.getElementById("semredo").onclick = semRedo;
    document.getElementById("nsemundo").onclick = semUndo;
    document.getElementById("nsemredo").onclick = semRedo;
    document.getElementById("checkall").onchange = checkAll;
    document.getElementById("deleteblocksrows").onclick = deleteRows;

    //listen for any form updates and modify json accordingly. n.b. in memory save does not validate form data
    listenForInputs();

    //Persist form's data in a browser's Local Storage and never loose them on occasional tabs closing, browser crashes and other disasters
    $('#todo-list').sisyphus({
      timeout: 10
    });

  }

  function listenForInputs(){
    $('#todo-list').on(
      "change", ".new-concept,.new-range,.new-meaning", function() {
        var jsid = $(this).closest("tr").attr('id');
        var classArray = $(this).closest("input").attr('class').split(/\s+/);
        var newVal =  $(this).closest("input").val();
        console.log("Current Sheet: "+ Current.getSheetNum());
        console.log("updating after two seconds");
        setTimeout(function() {
          updateJSON(jsid, classArray, newVal, Current.getSheetNum());
        }, 2000);
      }
    );
  }

  function updateJSON(jsid, classArray, newVal, currentSheetNum){
    
    if (jQuery.inArray("new-concept",classArray) !==-1){
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        if (mockdata.sheets[currentSheetNum].idx === jsid) {
          mockdata.sheets[currentSheetNum].name = newVal;
          break;
        }
      }
    }
    else if (jQuery.contains("new-range",classArray) !==-1){
    if (jQuery.inArray("new-range",classArray) !==-1){
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        if (mockdata.sheets[currentSheetNum].idx === jsid) {
          mockdata.sheets[currentSheetNum].range = newVal;
          break;
        }
      }
    }
    }
    else if (jQuery.contains("new-meaning",classArray) !==-1){
    if (jQuery.inArray("new-meaning",classArray) !==-1){
      for (var i=0; i<mockdata.sheets[currentSheetNum].sheetData.length; i++) {
        if (mockdata.sheets[currentSheetNum].idx === jsid) {
          mockdata.sheets[currentSheetNum].meaning = newVal;
          break;
        }
      }
    }
    }
    else{
      console.log("Cannot recognize the input type yet.")
    }
    console.log("JSON updated");
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

  function fillBlocksTable(num){
    $("#todo-list").empty();

    var temprow = "{{#sheetData}}<tr id={{idx}}><td><input type=\"checkbox\"><\/td><td><input type=\"text\" value={{name}} class=\"span12 new-concept\"><\/td><td><input type=\"text\" value={{range}} class=\"new-range span12\"><\/td>\r\n<td><span class=\"span16 uri new-meaning\" type=\"text\">{{meaning}}<\/span><\/td><\/tr>{{/sheetData}}";
    
    if (num == null){
      num = 0;
    } 
    
    var htmlrow = $.parseHTML(Mustache.render(temprow, mockdata.sheets[num]));
    Current.setSheetNum(num);
    
    $("#todo-list").append(htmlrow);
  }

  function fillRelationsTable(num){

  }

  //adds current length + 1 as the id of the new json node and appends a new blank row to the form
  function addBlocksItem(){
    var newID = mockdata.sheets[Current.getSheetNum()].length+1;
    var temprow = "<tr id="+ newID +"><td><input type=\"checkbox\"><\/td><td><input type=\"text\" placeholder=\"Bolt 1\" class=\"span12 new-concept\"><\/td><td><input type=\"text\" placeholder=\"sheet!A3:B6\" class=\"span12 new-range\"><\/td>\r\n<td><input class=\"span16 uri new-meaning\" type=\"text\" placeholder=\"URI\"><\/td><\/tr>"
    var htmlrow = $.parseHTML(temprow);
    $("#todo-list").append(htmlrow);
    Current.setSheetNum(newID);
  }

  function removeBlocksItem(){
    deleteRows(Current.getSheetNum());
  }

 function deleteRows(delID) {
     try {
         var table = document.getElementById("blockstable");
         var rowCount = table.rows.length;

         for (var i = 1; i < rowCount; i++) {
            var row = table.rows[i];
            var chkbox = row.cells[0].childNodes[0];
            if (delID==null){
              if (null != chkbox && true == chkbox.checked) {
                table.deleteRow(i);
                // $(chkbox).closest("tr").remove();
                rowCount--;
                i--;
              }
            }
            else{
              if (i === delID){
                table.deleteRow(i);
                rowCount--;
                i--;                
              }
            }
          
        }
     } catch (e) {
         console.log(e);
     }
 }


