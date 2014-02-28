var mockdata = {
  "SimplePricingxlsx" : {
    "vendor" : [
      {
        "name" : "Price",
        "range" : "A4:A11",
        "meaning" : "blahblah"      
      },
      {
        "name" : "Price",
        "range" : "A4:A12",
        "meaning" : "blahblah"      
      },
      {
       "name" : "Price",
        "range" : "A4:A13",
        "meaning" : "blahblah"      
      }
    ],
    "customer" : [
      {
        "name" : "CustomerA",
        "range" : "A3:A9",
        "meaning" : "Price per piece"      
      },
      {
        "name" : "Price",
        "range" : "A4:A11",
        "meaning" : "blahblah"      
      },
      {
        "name" : "CustomerA",
        "range" : "A3:A9",
        "meaning" : "Price per piece"      
      }

    ]
  }
};

// generates the block table contents
// $.getJSON('mockjsonfromsally.json', function(mockdata){

	var trsfrag = document.createDocumentFragment();
	var tdsfrag = document.createDocumentFragment();

	var tr = document.createElement('tr');
	var emptd = document.createElement('td');

	var templatetd;

	// append empty td to tdsfrag
	tdsfrag.appendChild(emptd); 

	//cached elements for appending to the frags
	var input = document.createElement('input');
	var span = document.createElement('span');

	//TODO grab these attributes from the placeholder row in the html page instead of redefining for consistency
	var inputConcept = setAttributes(input, {'id':'new-concept', 'type':'text', 'class':'span12'});
	var inputRange = setAttributes(input, {'id':'new-range', 'type':'text', 'class':'span12'});
	var spanUri = setAttributes(span, {'id':'new-meaning', 'type':'text', 'class':'span16 uri'});


	for(var i in mockdata.SimplePricingxlsx.vendor){
		//new-concept
		templatetd = emptd;
		inputConcept.setAttribute('value',mockdata.SimplePricingxlsx.vendor[i].name);
		templatetd.appendChild(inputConcept);
		tdsfrag.appendChild(templatetd);

		//new-range
		templatetd = emptd;
		inputRange.setAttribute('value',mockdata.SimplePricingxlsx.vendor[i].range);
		templatetd.appendChild(inputRange);
		tdsfrag.appendChild(templatetd);

		//new-meaning
		templatetd = emptd;
		spanUri.setAttribute('value',mockdata.SimplePricingxlsx.vendor[i].meaning);
		templatetd.appendChild(spanUri);
		tdsfrag.appendChild(templatetd);
	}
	tr.appendChild(tdsfrag);
	trsfrag.appendChild(tr);

	window.onload = tblappender;
	function tblappender(){
		var tbody = document.getElementById("todo-list");
		tbody.appendChild(trsfrag);	
	}
	
//});

function setAttributes(el, attrs) {
  for(var key in attrs) {
    el.setAttribute(key, attrs[key]);
  }
  return el;
}



var mockdata = [
                  {
                      "workbook": {
                          "bookname":"SimplePricingxlsx",

                          "vendor": [
                              {
                                  "name": "Price",
                                  "range": "A4:A11",
                                  "meaning": "blahblah"
                              },
                              {
                                  "name": "Price",
                                  "range": "A4:A12",
                                  "meaning": "blahblah"
                              },
                              {
                                  "name": "Price",
                                  "range": "A4:A13",
                                  "meaning": "blahblah"
                              }
                          ],
                          "customer": [
                              {
                                  "name": "CustomerA",
                                  "range": "A3:A9",
                                  "meaning": "Price per piece"
                              },
                              {
                                  "name": "Price",
                                  "range": "A4:A11",
                                  "meaning": "blahblah"
                              },
                              {
                                  "name": "CustomerC",
                                  "range": "A3:A9",
                                  "meaning": "Price per piece"
                              }
                          ]
                        }
                      
                  }
              ];