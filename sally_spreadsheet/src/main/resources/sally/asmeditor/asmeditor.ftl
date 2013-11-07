<!DOCTYPE html>
<html>
<head>
<script src="/sally/lib/jquery/jquery.js"></script>

<script>
//if (typeof(console) == null) {
	$("head").append($("<script>").attr("type","text/javascript").attr("src", "/sally/firebug.js"));
//}
</script>


<script src="http://localhost:8181/sally/comm/protobuf.js"></script>
<script src="http://localhost:8181/sally/comm/communication.js"></script>
<script src="http://localhost:8181/sally/comm/common.js"></script>
<script src="http://localhost:8181/sally/comm/util.js"></script>


<script src="/sally/underscore/underscore.js"></script>
<script src="/sally/backbone/backbone.js"></script>
<script src="/sally/asmeditorlib/asmajaxadaptor.js"></script>
<script src="/sally/jobad/build/release/libs/js/libs.js"></script>
<script src="/sally/jobad/build/release/JOBAD.min.js"></script>
<meta name="viewport" content="width=device-width, initial-scale=1.0">

<link href="/sally/jobad/build/release/libs/css/libs.css"
	rel="stylesheet">
<link href="/sally/jobad/build/release/JOBAD.css" rel="stylesheet">

<link href="/sally/asmeditorlib/asmeditor.css" rel="stylesheet">
<link href="/sally/bootstrap_tree.css" rel="stylesheet">
<!-- <script src="/sally/bootstrap_tree.js"></script> -->
<script>
	WEB = {};
	exports = {};
</script>

<link href="/sally/asmeditorlib/todos.css" rel="stylesheet">
<script src="/sally/asmeditorlib/todos.js"></script>
<script src="/sally/asmeditorlib/json3.js"></script>
<script src="/sally/asmeditorlib/asmeditor.js"></script>
<script src="/sally/asmeditorlib/asmeditorui.js"></script>

<script>
	asmeditor = new ASMEditor(asm);
	refresh_tree();
</script>

<script type="text/template" id="item-template">
<td>
</td>
<td class="">
    <div class="view-name">
      <label class="view"><%- name %></label> 
      <input class="edit span12" type="text" value="<%- name %>" />
    </div>
   </td>
<td class="">
    <div class="view-range">
      <label class="view"><%- range %></label>  
      <input class="edit span12" type="text" value="<%- range %>" />
    </div>
</td>
<td class="">
    <div class="view-meaning">
      <label class="view"><%- meaning %></label> 
      <input class="edit span12" type="text" value="<%- meaning %>" />
    </div>
</td>
  </script>

<style type="text/css">
body {
	padding-top: 30px;
	padding-bottom: 40px;
}

.sidebar-nav {
	padding: 9px 0;
}

@media ( max-width : 980px) {
	/* Enable use of floated navbar text */
	.navbar-text.pull-right {
		float: none;
		padding-left: 5px;
		padding-right: 5px;
	}
}
</style>

</head>

<body class="bootstrap">

	<div class="navbar navbar-fixed-top">
		<div class="navbar-inner">
			<div class="container-fluid">
				<button type="button" class="btn btn-navbar" data-toggle="collapse"
					data-target=".nav-collapse">
					<span class="icon-bar"></span> <span class="icon-bar"></span> <span
						class="icon-bar"></span>
				</button>
				<div class="nav-collapse collapse">
					<ul class="nav">
						<li class="active"><a href="#">Blocks</a></li>
						<li><a href="#relations">Relations</a></li>
					</ul>
				</div>
				<!--/.nav-collapse -->
			</div>
		</div>
	</div>

	<div class="container-fluid">
		<div class="row-fluid">
			<div class="span10"></div>
			<div class="span2">
				http://localhost:8181/sally/asmeditor?pid=${token}</div>
		</div>

		<div class="row-fluid">
			<div class="span3">
				<div class="well compact">
					<h4>Workbooks</h4>
					<div class="tree compact">
						<ul id="block-spread-root" class="compact">
						</ul>
					</div>
				</div>
			</div>

			<div class="span9">

				<div id="todoapp">
					<div class="row-fluid">
						<div class="span9">
							<div class="btn-toolbar">
								<div class="btn-group">
									<button type="button" class="btn btn-default">Undo</button>
									<button type="button" class="btn btn-default">Redo</button>
								</div>

								<div class="btn-group">
									<button type="button" class="btn btn-default add-btn">Add</button>
									<button type="button" class="btn btn-default">Delete</button>
									<button type="button" class="btn btn-default">Merge</button>
								</div>
							</div>
						</div>
						<div class="span3">
							<div class="btn-toolbar">
								<div class="btn-group">
									<button type="button" class="btn btn-default">Auto</button>
									<button type="button" class="btn btn-default">Value</button>
								</div>
							</div>
						</div>
					</div>

					<section id="main">
						<table class="table">
							<thead>
								<tr>
									<td class="span1"></td>
									<td colspan="3">Blocks</td>
								</tr>
								<tr>
									<th class="span1"></th>
									<th class="span3">Name</th>
									<th class="span3">Range</th>
									<th class="span3">Concept</th>
									<th class="span2"></th>
								</tr>
							</thead>
							<tbody id="todo-list">
								<tr>
									<td></td>
									<td><input id="new-concept" type="text" value="bolt1"
										placeholder="Bolt 1" class="span12"></td>
									<td><input id="new-range" type="text" value="sheet!A3:B6"
										placeholder="sheet!A3:B6" class="span12"></td>
									<td><span class="span12 uri" id="new-meaning" type="text"
										placeholder="Bolt" class="span12">http://docs.omdoc.org/cad/ISOhexbolt.omdoc?ISOhexbolt?ISO-hex-bolt</span></td>
								</tr>
							</tbody>
						</table>
					</section>

				</div>

				<div class="row-fluid" id="block-page"></div>

				<div id="test"></div>

				<script language="javascript">
				Communication.injectScripts();
				</script>

			</div>
			<!--/span-->
		</div>
		<!--/row-->

	</div>
</body>
</html>