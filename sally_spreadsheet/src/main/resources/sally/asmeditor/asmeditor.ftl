<!DOCTYPE html>
<html>
<head>
<script src="/sally/jobad/build/release/libs/js/libs.js"></script>
<script src="/sally/jobad/build/release/JOBAD.min.js"></script>
<meta name="viewport" content="width=device-width, initial-scale=1.0">

<link href="/sally/jobad/build/release/libs/css/libs.css"
	rel="stylesheet">
<link href="/sally/jobad/build/release/JOBAD.css" rel="stylesheet">

<link href="/sally/bootstrap_tree.css" rel="stylesheet">
<!-- <script src="/sally/bootstrap_tree.js"></script> -->
<script>
	WEB = {};
	exports = {};
</script>

<script src="/sally/asmeditorlib/json3.js"></script>
<script src="/sally/asmeditorlib/asmeditor.js"></script>
<script src="/sally/asmeditorlib/asmeditorui.js"></script>

<script>
	asmeditor = new ASMEditor(asm);
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
			<div class="span10">
				<div class="btn-toolbar">
					<div class="btn-group">
						<button type="button" class="btn btn-default">Undo</button>
						<button type="button" class="btn btn-default">Redo</button>
					</div>
				</div>
			</div>
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

			<script>
			</script>

			<div class="span9">
				<div class="row-fluid" id="block-page"></div>

				<div id="test"></div>

				<script language="javascript">
					open_sheet("SimplePricing.xlsx", "vendor prices");

					window.mylog = function(text) {
						$("#test").append(text);
					}

					
					setTimeout(function() {
						mylog(typeof(app.injectScripts));
						app.injectScripts();
					}, 300);

					refresh_tree();

				</script>

			</div>
			<!--/span-->
		</div>
		<!--/row-->

	</div>
</body>
</html>