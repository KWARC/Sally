/*
	example2.js - An example module for JOBAD. 
	Provides a context menu entry which checks if the clicked element is a <p>. 
	
	Copyright (C) 2013 KWARC Group <kwarc.info>
	
	This file is part of JOBAD.
	
	JOBAD is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.
	
	JOBAD is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.
	
	You should have received a copy of the GNU General Public License
	along with JOBAD.  If not, see <http://www.gnu.org/licenses/>.
*/
(function($){
	JOBAD.modules.register({
		info:{
			'identifier':	'test.menu1',
			'title':	'Paragraphs Module',
			'author':	'Tom Wiesing',
			'description':	'Provides a context menu entry which checks if the clicked element is a <p>. '
		},
		globalinit: function(){
			//source: http://openiconlibrary.sourceforge.net/gallery2/?./Icons/status/dialog-declare.png (license: GPLv2)
			JOBAD.resources.provide("icon", "test.question", "data:image/png;base64,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etv/2tGmz21zv3Usl7MPV2o17ovk+O8AEqnJMVF8CJhxDK2Stk1CTNc4GkUTZdbD6m/f295YXvvrmyv+L9H6u9ZBGB92uEvu6vx2bhL3I8/7VCFnz1TrVRZKxFvEFOjMh1IHXFq/rvcV36d+/HlT55gqWSizHlauXGot3/rwtfb25t96N/9+fZx1HpUAgKuitfK1dXvi3mbUbR/OO/psrV7lTNMRRBJqcKa5Pxp8BOTAQiNWyls6ZiomCrKDld9e2lm/ufwahdrfrLz3izt4yAPAR3zAcTFsr31xtVRtfdjrtBsaovlGtWzk8zkoxJsXRVmRYvWTqpJRfwjcNjQ0iiZmChyyuaY+uvL+8tqd1Veb6L2++u6rDwX/OxAAgHfD5trXVoy6eyX0miLc250rWFqxPlFihZwFztlgQ98nwFjK95xB4wyGxlGwdDSKFqaLGnKig+3bV72Prn3wbnN952e31nr/4P3Xz1ceZJuMUI9OYEh6dvb7M9pROlfMF8+XGvXnyzOH6061oQndgS85Qhl3aaKh6pbO4RgctkawmIBw29TeXPN3Vldu7DXbb+757Jdr/7G+9Id+Spla553qGWe+YthnbCv/Yq5c+ROnPDFnl0qOlStommUzTTcYGAMnBSVCEn5Phd1O5LZau93W7lKv23k79K23P2zevobrb7bwezzw/kSe1M8/59Ys7i5K0o87ee2EbpiLnGt1phs5RsQAipSSrSiINkI/uiWF+oCHpRu3o9XNZDz433hSv29pwAUN2HAOHao5nrNZlLmqWQHQNgKpewi3ZkQX0ZKHixdDAOHHvN//rz+K9d9RpiYa4ycH5gAAAB10RVh0Q29tbWVudABDcmVhdGVkIHdpdGggVGhlIEdJTVDvZCVuAAAAJXRFWHRjcmVhdGUtZGF0ZQAyMDA5LTExLTE3VDIwOjA2OjU4LTA3OjAwOHFLewAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAxMC0wMi0yMFQxOToyMjo0Mi0wNzowMMSpj+wAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMTAtMDEtMTFUMTQ6MTk6NDYtMDc6MDA5MaJ3AAAANHRFWHRMaWNlbnNlAGh0dHA6Ly9jcmVhdGl2ZWNvbW1vbnMub3JnL2xpY2Vuc2VzL0dQTC8yLjAvbGoGqAAAACV0RVh0bW9kaWZ5LWRhdGUAMjAwOS0xMS0xN1QyMDowNjo1OC0wNzowMGfAPU8AAAAYdEVYdFNvdXJjZQBJbnRyaWd1ZSBJY29uIFNldK4noT8AAABGdEVYdFNvdXJjZV9VUkwAaHR0cDovL3NpbXBsZWlubm92YXRpb24ubmV0L2luZGV4LnBocD9wYWdlPTIyJnNvdXJjZT0yJmlkPTKVQfnGAAAAAElFTkSuQmCC")
		},
		contextMenuEntries: function(target){
			if(target.is('#nomenu,#nomenu *')){ //no menu for these elements
				return false;
			}
			return [
				["Am I a <p> ?", function(element){
					if(element.is("p")){
						alert("I am a <p> element. ");
					} else {
						alert("No I'm not. ");
					}
				}, "test.question"]
			];
		}
	});
})(JOBAD.refs.$);
