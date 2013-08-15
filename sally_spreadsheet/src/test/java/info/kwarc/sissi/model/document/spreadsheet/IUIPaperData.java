package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.model.document.spreadsheet.ASMInterface;

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.codec.binary.Base64;

import sally.CellData;
import sally.CellPosition;
import sally.DataParameter;
import sally.FBCreateData;
import sally.LegendCreateData;
import sally.RangeData;
import sally.RangeData.Builder;
import sally.SpreadsheetModel;

import com.hp.hpl.jena.rdf.model.Model;

public class IUIPaperData {
	ASMInterface asm;

	public IUIPaperData() {
		asm = new ASMInterface("http://iui-paper");
	}

	Integer createRowFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		return createFB(sheet, startRow, startCol, startRow, startCol+content.length-1, new String[][] {content}, ids);
	}

	Integer createColFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		String [][] c = new String[content.length][1];
		for (int i=0; i<content.length; ++i)
			c[i][0] = content[i];
		return createFB(sheet, startRow, startCol, startRow+content.length-1, startCol, c, ids);
	}

	Integer createFB(int sheet, int startRow, int startCol, int endRow, int endCol, String [][] content, Integer [] ids) {
		startRow--;endRow--;startCol--;endCol--;
		FBCreateData.Builder createData = FBCreateData.newBuilder();
		RangeData.Builder range = RangeData.newBuilder();
		for (int i=startRow; i<=endRow; ++i) {
			for (int j=startCol; j<=endCol; ++j) {
				CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(j).setRow(i).build()).build()).setValue(content[i-startRow][j-startCol]).build();
				range.addCells(data);
			}
		}
		createData.setRange(range.build());
		List<Integer> list = Arrays.asList(ids); 
		createData.addAllLegends(list);
		createData.setParameter(DataParameter.SameContentSameElement);
		return asm.createFB(createData.build());
	}

	// This should be used for header and titles of data
	Integer setHeaderLabel(int sheet, int startRow, int startCol, int length, String text) {
		String [] names = new String[length];
		for (int i=0; i<length; ++i)
			names[i] = text;
		return setRowTableHeaders(sheet, startRow, startCol, names);
	}

	Integer setRowTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		startRow--;startCol--;
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(i+startCol).setRow(startRow).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	Integer setColTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		startRow--;startCol--;
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(startCol).setRow(startRow+i).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	public void setData() {
		//buildPricingSheet();
		//buildVendorA();
		//buildVendorB();
		//buildVendorC();
		
		buildContractCoolingSystem();
	}
	
	static final String boltURI="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/nutbolt.omdoc?nutbolt?bolt";
	static final String nutURI="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexnut.omdoc?ISOhexnut?ISO-hex-nut";
	static final String gasketURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?flange-gasket";
	static final String flangeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?flange";
	static final String blindFlangeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?blind-flange";
	
	static final String partNoURI ="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/partnumber.omdoc?partnumber?part-number";  
	static final String threadTypeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOmetricthread.omdoc?ISOmetricthread?sISOhexthread";
	static final String colorURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/colors.omdoc?color?color";
	static final String headTypeURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?head";
	static final String costURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?cost";
	static final String gasketType = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/flange-bolt-gasket.omdoc?flange-bolt-gasket?gasket-type";

	static final String vendorURI = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendor.omdoc?vendor?vendor";

	public void buildPricingSheet() {
		Integer workSheetid = asm.getWorksheetIDByName("Pricing");

		Integer tableProps = setRowTableHeaders(workSheetid, 6, 1, new String[] {"Component", "Thread", "Color", "Head", "Type", "Quantity per flange", ""});

		Integer componentCol = setColTableHeaders(workSheetid, 8, 1, new String[] {"bolt", "nut", "gasket", "flange", "blind flange"});
		Integer threadCol = setColTableHeaders(workSheetid, 8, 2, new String[] { "M10", "M10", "_", "M10", "M10"});
		Integer colorCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "black", "black", "_", "black", "black"});
		Integer headCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "machine", "_", "_", "_", "_"});
		Integer typeCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "_", "_", "standard", "_", "_"});
		Integer quantityCol = setColTableHeaders(workSheetid, 8, 6, new String[] { "6", "6", "1", "1", "1"});

		Integer vendorA = setHeaderLabel(workSheetid, 5, 7, 2, "Vendor A");
		Integer vendorB = setHeaderLabel(workSheetid, 5, 9, 2, "Vendor B");
		Integer vendorC = setHeaderLabel(workSheetid, 5, 11, 2, "Vendor C");
		
		Integer costByPieceVendorA = createColFB(workSheetid, 8, 7, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		Integer costTotalVendorA = createColFB(workSheetid, 8, 8, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorA});
		Integer costByPieceVendorB = createColFB(workSheetid, 8, 9, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		Integer costTotalVendorB = createColFB(workSheetid, 8, 10, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorB});
		Integer costByPieceVendorC = createColFB(workSheetid, 8, 11, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});
		Integer costTotalVendorC = createColFB(workSheetid, 8, 12, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol, quantityCol, vendorC});

		asm.addOntologyLink(componentCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/components.omdoc?component?component");
		asm.addOntologyLink(threadCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexthread.omdoc?ISOhexthread?ISOhexthread");
		asm.addOntologyLink(colorCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/colors.omdoc?color?color");
		asm.addOntologyLink(headCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/ISOhexbolt.omdoc?ISOhexbolt?head");
		asm.addOntologyLink(typeCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/comp_types.omdoc?comptype?comptype");
		asm.addOntologyLink(quantityCol, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/quantity.omdoc?quantity?quantity");

		asm.addOntologyLink(vendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?A");
		asm.addOntologyLink(vendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?B");
		asm.addOntologyLink(vendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/vendors.omdoc?vendors?C");
		
		asm.addOntologyLink(costByPieceVendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorA, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		asm.addOntologyLink(costByPieceVendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorB, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		asm.addOntologyLink(costByPieceVendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?bypiece");
		asm.addOntologyLink(costTotalVendorC, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/cost.omdoc?cost?total");
		
	}
	
	public void buildVendorA() {
		Integer workSheetid = asm.getWorksheetIDByName("Vendor A");
		
		Integer vendA = setHeaderLabel(workSheetid, 1, 1, 8, "Price List of Vendor A");
		asm.addOntologyLink(vendA, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?seller");
		
		Integer discountMinQuantity = setRowTableHeaders(workSheetid, 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		Integer discountRatesFB = createRowFB(workSheetid, 5, 1, new String[] {"100.000%", "99.000%", "95.000%", "90.000%"}, new Integer [] {vendA, discountMinQuantity});
		//asm.addOntologyLink(discountMinQuantity, "http://info.kwarc.sissi.winograd/discount-min-quantities");
		asm.addOntologyLink(discountMinQuantity,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?minimum-purchase");
		//asm.addOntologyLink(discountRatesFB, "http://info.kwarc.sissi.winograd/discount-rates");
		asm.addOntologyLink(discountRatesFB,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?discount");
		
		//Integer tableProps = setRowTableHeaders(workSheetid, 7, 1, new String[] {"Part No", "Component", "Thread", "Color", "Head", "Type", "Basic Price"});
		Integer vendorA = setColTableHeaders(workSheetid, 8, 9, new String[] {"Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A", "Vendor A"});
		
		Integer boltsCol = setColTableHeaders(workSheetid, 8, 2, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt"});
		Integer boltThreadCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "M10", "M10", "M10", "M10", "M10", "M10", "M16", "M16"});
		Integer boltColorCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "silver", "silver", "black", "silver", "red", "black", "black", "black"});
		Integer boltHeadCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "carriage", "stove", "machine", "machine", "machine", "machine", "machine", "machine"});
		Integer boltCostCol = setColTableHeaders(workSheetid, 8, 7, new String[] {"0.450 EUR", "0.460 EUR", "0.300 EUR", "0.310 EUR", "0.340 EUR", "0.350 EUR", "0.300 EUR", "0.350 EUR"});
		
		Integer boltPartNo = createColFB(workSheetid, 8, 1, new String[] {"a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8"}, 
				new Integer[]{boltsCol, boltThreadCol, boltColorCol, boltHeadCol, boltCostCol, vendorA});

		//asm.addOntologyLink(tableProps, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/component.omdoc?component?ids");
		asm.addOntologyLink(boltPartNo, partNoURI);
		asm.addOntologyLink(boltsCol, boltURI);
		asm.addOntologyLink(boltThreadCol, threadTypeURI);
		asm.addOntologyLink(boltColorCol, colorURI);
		asm.addOntologyLink(boltHeadCol, headTypeURI);
		asm.addOntologyLink(boltCostCol, costURI);
		asm.addOntologyLink(vendorA, vendorURI);


		Integer nutCol = setColTableHeaders(workSheetid, 16, 2, new String[] {"nut", "nut"});
		Integer nutThreadCol = setColTableHeaders(workSheetid, 16, 3, new String[] { "M10", "M12"});
		Integer nutColorCol = setColTableHeaders(workSheetid, 16, 4, new String[] { "black", "black"});
		Integer nutCostCol = setColTableHeaders(workSheetid, 16, 7, new String[] {"0.450 EUR", "0.460 EUR"});
		Integer nutPartNo = createColFB(workSheetid, 16, 1, new String[] {"a9", "a10"}, new Integer[]{nutCol, nutThreadCol, nutColorCol, nutCostCol, vendorA});

		asm.addOntologyLink(nutCol, nutURI);
		asm.addOntologyLink(nutThreadCol, threadTypeURI);
		asm.addOntologyLink(nutColorCol, colorURI);
		asm.addOntologyLink(nutCostCol, costURI);
		asm.addOntologyLink(nutPartNo, partNoURI);

		Integer gasketCol = setColTableHeaders(workSheetid, 18, 2, new String[] {"gasket"});
		Integer gasketTypeCol = setColTableHeaders(workSheetid, 18, 6, new String[] {"standard"});
		Integer gasketCost = setColTableHeaders(workSheetid, 18, 7, new String[] {"2.040 EUR"});
		Integer gasketPartNo = createColFB(workSheetid, 18, 1, new String[] {"a11"}, new Integer[]{gasketCol, gasketTypeCol, gasketCost, vendorA});
		
		asm.addOntologyLink(gasketCol, gasketURI);
		asm.addOntologyLink(gasketTypeCol, gasketType);
		asm.addOntologyLink(gasketCost, costURI);
		asm.addOntologyLink(gasketPartNo, partNoURI);

		Integer flangeCol = setColTableHeaders(workSheetid, 19, 2, new String[] {"flange", "flange", "flange"});
		Integer flangeThreadCol = setColTableHeaders(workSheetid, 19, 3, new String[] { "M10", "M10", "M16"});
		Integer flangeColorCol = setColTableHeaders(workSheetid, 19, 4, new String[] { "black", "silver", "black"});
		Integer flangeCostCol = setColTableHeaders(workSheetid, 19, 7, new String[] {"1.080 EUR", "1.080 EUR", "1.090 EUR"});
		Integer flangePartNo = createColFB(workSheetid, 19, 1, new String[] {"a12", "a13", "a14"}, new Integer[]{flangeCol, flangeThreadCol, flangeColorCol, flangeCostCol, vendorA});

		asm.addOntologyLink(flangeCol, flangeURI);
		asm.addOntologyLink(flangeThreadCol, threadTypeURI);
		asm.addOntologyLink(flangeColorCol, colorURI);
		asm.addOntologyLink(flangeCostCol, costURI);
		asm.addOntologyLink(flangePartNo, partNoURI);

		Integer blindflangeCol = setColTableHeaders(workSheetid, 22, 2, new String[] {"blind-flange", "blind-flange", "blind-flange"});
		Integer blindflangeThreadCol = setColTableHeaders(workSheetid, 22, 3, new String[] { "M10", "M16", "M17"});
		Integer blindflangeColorCol = setColTableHeaders(workSheetid, 22, 4, new String[] { "black", "black", "black"});
		Integer blindflangeCostCol = setColTableHeaders(workSheetid, 22, 7, new String[] {"0.888 EUR", "0.888 EUR", "0.888 EUR"});
		Integer blindflangePartNo = createColFB(workSheetid, 22, 1, new String[] {"a15", "a16", "a17"}, new Integer[]{blindflangeCol, blindflangeThreadCol, blindflangeColorCol, blindflangeCostCol, vendorA});

		asm.addOntologyLink(blindflangeCol, blindFlangeURI);
		asm.addOntologyLink(blindflangeThreadCol, threadTypeURI);
		asm.addOntologyLink(blindflangeColorCol, colorURI);
		asm.addOntologyLink(blindflangeCostCol, costURI);
		asm.addOntologyLink(blindflangePartNo, partNoURI);
	}
	
	public void buildVendorB() {
		Integer workSheetid = asm.getWorksheetIDByName("Vendor B");
		
		Integer vendB = setHeaderLabel(workSheetid, 1, 1, 8, "Price List of Vendor B");
		asm.addOntologyLink(vendB, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?seller");
		
		
		Integer discountMinQuantity = setRowTableHeaders(workSheetid, 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		Integer discountRatesFB = createRowFB(workSheetid, 5, 1, new String[] {"100.000%", "96.000%", "92.000%", "90.000%"}, new Integer [] {vendB, discountMinQuantity});
		asm.addOntologyLink(discountMinQuantity,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?minimum-purchase");
		asm.addOntologyLink(discountRatesFB,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?discount");
		
		//Integer tableProps = setRowTableHeaders(workSheetid, 7, 1, new String[] {"Part No", "Component", "Thread", "Color", "Head", "Type", "Basic Price"});
		Integer vendorB = setColTableHeaders(workSheetid, 8, 9, new String[] {"Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B", "Vendor B"});		
		
		Integer boltsCol = setColTableHeaders(workSheetid, 8, 2, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt"});
		Integer boltThreadCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "M10", "M10", "M10", "M10", "M10", "M10", "M12", "M16"});
		Integer boltColorCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "silver", "red", "black", "silver", "red", "red", "black", "red"});
		Integer boltHeadCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "carriage", "stove", "machine", "machine", "machine", "carriage", "machine", "stove"});
		Integer boltCostCol = setColTableHeaders(workSheetid, 8, 7, new String[] {"0.440 EUR", "0.465 EUR", "0.350 EUR", "0.320 EUR", "0.370 EUR", "0.360 EUR", "0.400 EUR", "0.350 EUR"});
		
		Integer boltPartNo = createColFB(workSheetid, 8, 1, new String[] {"b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8"}, 
				new Integer[]{boltsCol, boltThreadCol, boltColorCol, boltHeadCol, boltCostCol, vendorB});

		//asm.addOntologyLink(tableProps, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/component.omdoc?component?ids");
		asm.addOntologyLink(boltPartNo, partNoURI);
		asm.addOntologyLink(boltsCol, boltURI);
		asm.addOntologyLink(boltThreadCol, threadTypeURI);
		asm.addOntologyLink(boltColorCol, colorURI);
		asm.addOntologyLink(boltHeadCol, headTypeURI);
		asm.addOntologyLink(boltCostCol, costURI);
		asm.addOntologyLink(vendorB, vendorURI);


		Integer nutCol = setColTableHeaders(workSheetid, 16, 2, new String[] {"nut", "nut","nut", "nut"});
		Integer nutThreadCol = setColTableHeaders(workSheetid, 16, 3, new String[] { "M10", "M10","M12", "M10"});
		Integer nutColorCol = setColTableHeaders(workSheetid, 16, 4, new String[] { "red", "silver", "black", "black"});
		Integer nutCostCol = setColTableHeaders(workSheetid, 16, 7, new String[] {"0.518 EUR", "0.518 EUR","0.498 EUR", "0.500 EUR"});
		Integer nutPartNo = createColFB(workSheetid, 16, 1, new String[] {"b9", "b10","b11", "b12"}, new Integer[]{nutCol, nutThreadCol, nutColorCol, nutCostCol, vendorB});

		asm.addOntologyLink(nutCol, nutURI);
		asm.addOntologyLink(nutThreadCol, threadTypeURI);
		asm.addOntologyLink(nutColorCol, colorURI);
		asm.addOntologyLink(nutCostCol, costURI);
		asm.addOntologyLink(nutPartNo, partNoURI);

		Integer gasketCol = setColTableHeaders(workSheetid, 20, 2, new String[] {"gasket"});
		Integer gasketTypeCol = setColTableHeaders(workSheetid, 20, 6, new String[] {"standard"});
		Integer gasketCost = setColTableHeaders(workSheetid, 20, 7, new String[] {"2.000 EUR"});
		Integer gasketPartNo = createColFB(workSheetid, 20, 1, new String[] {"b13"}, new Integer[]{gasketCol, gasketTypeCol, gasketCost, vendorB});
		
		asm.addOntologyLink(gasketCol, gasketURI);
		asm.addOntologyLink(gasketTypeCol, gasketType);
		asm.addOntologyLink(gasketCost, costURI);
		asm.addOntologyLink(gasketPartNo, partNoURI);

		Integer flangeCol = setColTableHeaders(workSheetid, 21, 2, new String[] {"flange", "flange"});
		Integer flangeThreadCol = setColTableHeaders(workSheetid, 21, 3, new String[] { "M10", "M12"});
		Integer flangeColorCol = setColTableHeaders(workSheetid, 21, 4, new String[] { "black", "black"});
		Integer flangeCostCol = setColTableHeaders(workSheetid, 21, 7, new String[] {"1.400 EUR", "1.425 EUR"});
		Integer flangePartNo = createColFB(workSheetid, 21, 1, new String[] {"b14", "b15"}, new Integer[]{flangeCol, flangeThreadCol, flangeColorCol, flangeCostCol, vendorB});

		asm.addOntologyLink(flangeCol, flangeURI);
		asm.addOntologyLink(flangeThreadCol, threadTypeURI);
		asm.addOntologyLink(flangeColorCol, colorURI);
		asm.addOntologyLink(flangeCostCol, costURI);
		asm.addOntologyLink(flangePartNo, partNoURI);

		Integer blindflangeCol = setColTableHeaders(workSheetid, 23, 2, new String[] {"blind-flange", "blind-flange"});
		Integer blindflangeThreadCol = setColTableHeaders(workSheetid, 23, 3, new String[] { "M10", "M12"});
		Integer blindflangeColorCol = setColTableHeaders(workSheetid, 23, 4, new String[] { "black", "black"});
		Integer blindflangeCostCol = setColTableHeaders(workSheetid, 23, 7, new String[] {"0.200 EUR", "0.250 EUR"});
		Integer blindflangePartNo = createColFB(workSheetid, 23, 1, new String[] {"b16", "b17"}, new Integer[]{blindflangeCol, blindflangeThreadCol, blindflangeColorCol, blindflangeCostCol, vendorB});

		asm.addOntologyLink(blindflangeCol, blindFlangeURI);
		asm.addOntologyLink(blindflangeThreadCol, threadTypeURI);
		asm.addOntologyLink(blindflangeColorCol, colorURI);
		asm.addOntologyLink(blindflangeCostCol, costURI);
		asm.addOntologyLink(blindflangePartNo, partNoURI);
	}
	
	public void buildVendorC() {
		Integer workSheetid = asm.getWorksheetIDByName("Vendor C");
		
		Integer vendC = setHeaderLabel(workSheetid, 1, 1, 8, "Price List of Vendor C");
		asm.addOntologyLink(vendC, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?seller");
		
		
		Integer discountMinQuantity = setRowTableHeaders(workSheetid, 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		Integer discountRatesFB = createRowFB(workSheetid, 5, 1, new String[] {"100.000%", "97.000%", "93.000%", "89.000%"}, new Integer [] {vendC, discountMinQuantity});
		asm.addOntologyLink(discountMinQuantity,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?minimum-purchase");
		asm.addOntologyLink(discountRatesFB,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?discount");
		
		//Integer tableProps = setRowTableHeaders(workSheetid, 7, 1, new String[] {"Part No", "Component", "Thread", "Color", "Head", "Type", "Basic Price"});
		Integer vendorC = setColTableHeaders(workSheetid, 8, 9, new String[] {"Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C", "Vendor C"});
		
		Integer boltsCol = setColTableHeaders(workSheetid, 8, 2, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt"});
		Integer boltThreadCol = setColTableHeaders(workSheetid, 8, 3, new String[] { "M10", "M10", "M10", "M10", "M10", "M10", "M12", "M12"});
		Integer boltColorCol = setColTableHeaders(workSheetid, 8, 4, new String[] { "silver", "red", "red", "silver", "black", "red", "black", "red"});
		Integer boltHeadCol = setColTableHeaders(workSheetid, 8, 5, new String[] { "carriage", "stove", "machine", "machine", "machine", "carriage", "machine", "stove"});
		Integer boltCostCol = setColTableHeaders(workSheetid, 8, 7, new String[] {"0.600 EUR", "0.400 EUR", "0.390 EUR", "0.300 EUR", "0.350 EUR", "0.365 EUR", "0.380 EUR", "0.320 EUR"});
		
		Integer boltPartNo = createColFB(workSheetid, 8, 1, new String[] {"c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8"}, 
				new Integer[]{boltsCol, boltThreadCol, boltColorCol, boltHeadCol, boltCostCol, vendorC});

		//asm.addOntologyLink(tableProps, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/component.omdoc?component?ids");
		asm.addOntologyLink(boltPartNo, partNoURI);
		asm.addOntologyLink(boltsCol, boltURI);
		asm.addOntologyLink(boltThreadCol, threadTypeURI);
		asm.addOntologyLink(boltColorCol, colorURI);
		asm.addOntologyLink(boltHeadCol, headTypeURI);
		asm.addOntologyLink(boltCostCol, costURI);
		asm.addOntologyLink(vendorC, vendorURI);


		Integer nutCol = setColTableHeaders(workSheetid, 16, 2, new String[] {"nut", "nut","nut", "nut"});
		Integer nutThreadCol = setColTableHeaders(workSheetid, 16, 3, new String[] { "M10", "M10","M10", "M12"});
		Integer nutColorCol = setColTableHeaders(workSheetid, 16, 4, new String[] { "red", "black","silver", "black"});
		Integer nutCostCol = setColTableHeaders(workSheetid, 16, 7, new String[] {"0.500 EUR", "0.500 EUR","0.550 EUR", "0.698 EUR"});
		Integer nutPartNo = createColFB(workSheetid, 16, 1, new String[] {"c9", "c10","c11", "c12"}, new Integer[]{nutCol, nutThreadCol, nutColorCol, nutCostCol, vendorC});

		asm.addOntologyLink(nutCol, nutURI);
		asm.addOntologyLink(nutThreadCol, threadTypeURI);
		asm.addOntologyLink(nutColorCol, colorURI);
		asm.addOntologyLink(nutCostCol, costURI);
		asm.addOntologyLink(nutPartNo, partNoURI);

		Integer gasketCol = setColTableHeaders(workSheetid, 20, 2, new String[] {"gasket"});
		Integer gasketTypeCol = setColTableHeaders(workSheetid, 20, 6, new String[] {"standard"});
		Integer gasketCost = setColTableHeaders(workSheetid, 20, 7, new String[] {"3.000 EUR"});
		Integer gasketPartNo = createColFB(workSheetid, 20, 1, new String[] {"c13"}, new Integer[]{gasketCol, gasketTypeCol, gasketCost, vendorC});
		
		asm.addOntologyLink(gasketCol, gasketURI);
		asm.addOntologyLink(gasketTypeCol, gasketType);
		asm.addOntologyLink(gasketCost, costURI);
		asm.addOntologyLink(gasketPartNo, partNoURI);

		Integer flangeCol = setColTableHeaders(workSheetid, 21, 2, new String[] {"flange", "flange"});
		Integer flangeThreadCol = setColTableHeaders(workSheetid, 21, 3, new String[] { "M10", "M10"});
		Integer flangeColorCol = setColTableHeaders(workSheetid, 21, 4, new String[] { "black", "silver"});
		Integer flangeCostCol = setColTableHeaders(workSheetid, 21, 7, new String[] {"1.104 EUR", "1.104 EUR"});
		Integer flangePartNo = createColFB(workSheetid, 21, 1, new String[] {"c14", "c15"}, new Integer[]{flangeCol, flangeThreadCol, flangeColorCol, flangeCostCol, vendorC});

		asm.addOntologyLink(flangeCol, flangeURI);
		asm.addOntologyLink(flangeThreadCol, threadTypeURI);
		asm.addOntologyLink(flangeColorCol, colorURI);
		asm.addOntologyLink(flangeCostCol, costURI);
		asm.addOntologyLink(flangePartNo, partNoURI);

		Integer blindflangeCol = setColTableHeaders(workSheetid, 23, 2, new String[] {"blind-flange", "blind-flange"});
		Integer blindflangeThreadCol = setColTableHeaders(workSheetid, 23, 3, new String[] { "M12", "M12"});
		Integer blindflangeColorCol = setColTableHeaders(workSheetid, 23, 4, new String[] { "black", "silver"});
		Integer blindflangeCostCol = setColTableHeaders(workSheetid, 23, 7, new String[] {"0.800 EUR", "0.800 EUR"});
		Integer blindflangePartNo = createColFB(workSheetid, 23, 1, new String[] {"c16", "c17"}, new Integer[]{blindflangeCol, blindflangeThreadCol, blindflangeColorCol, blindflangeCostCol, vendorC});

		asm.addOntologyLink(blindflangeCol, blindFlangeURI);
		asm.addOntologyLink(blindflangeThreadCol, threadTypeURI);
		asm.addOntologyLink(blindflangeColorCol, colorURI);
		asm.addOntologyLink(blindflangeCostCol, costURI);
		asm.addOntologyLink(blindflangePartNo, partNoURI);
	}

	public void buildContractCoolingSystem() {
		Integer workSheetid = asm.getWorksheetIDByName("Contract-MECS");
		String uriSize = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/five-sizes.omdoc?five-sizes?five-point-size-scale";
		//String uriQuantity = "https://tnt.kwarc.info/tntbase/stc/XHTMLBasicBrowser/slides/units/en/quantities.omdoc?quantities?quantity";
		String uriPrice ="https://tnt.kwarc.info/repos/stc/fcad/flange/cds/financial-transaction.omdoc?financial-transaction?transaction-price";
		String uriPartNo = "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/partnumber.omdoc?partnumber?part-number";
		
		Integer mesc = setHeaderLabel(workSheetid, 1, 1, 8, "Component Marine Engine Cooling System of Contract 12440628");
		asm.addOntologyLink(mesc, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/enclosed-cooling-system.omdoc?enclosed-cooling-system?enclosed-cooling-system");	
		
		
		//Seacock		
		Integer seacock_partMESC_ColName = setColTableHeaders(workSheetid, 4, 2, new String[] {"Seacock-2211", "Seacock-2211", "Seacock-2211"});
		Integer seacock_partMESC_ColSize = setColTableHeaders(workSheetid, 4, 3, new String[] {"S", "M", "XL"});
		Integer seacock_partMESC_ColPrice = setColTableHeaders(workSheetid, 4, 4, new String[] {"188.50 EUR", "328.50 EUR", "647.50 EUR"});
		Integer seacock_partMESC = createColFB(workSheetid, 4, 1, new String[] {"1244-2211-1", "1244-2211-2", "1244-2211-4"}, 
																  new Integer[]{seacock_partMESC_ColName, 
																				seacock_partMESC_ColSize, 
																				seacock_partMESC_ColPrice});
		asm.addOntologyLink(seacock_partMESC, uriPartNo);
		asm.addOntologyLink(seacock_partMESC_ColName, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/enclosed-cooling-system.omdoc?enclosed-cooling-system?seacock");
		asm.addOntologyLink(seacock_partMESC_ColSize, uriSize);
		asm.addOntologyLink(seacock_partMESC_ColPrice, uriPrice);
		
		//sea strainer
		Integer seastrainer_partMESC_ColName = setColTableHeaders(workSheetid, 7, 2, new String[] {"Sea Strainer-2207", "Sea Strainer-2207", "Sea Strainer-2207"});
		Integer seastrainer_partMESC_ColSize = setColTableHeaders(workSheetid, 7, 3, new String[] {"S", "L", "XL"});
		Integer seastrainer_partMESC_ColPrice = setColTableHeaders(workSheetid, 7, 4, new String[] {"120.00 EUR", "130.00 EUR", "140.00 EUR"});
		Integer seastrainer_partMESC = createColFB(workSheetid, 7, 1, new String[] {"1244-2207-1", "1244-2207-3", "1244-2207-4"}, 
																  new Integer[]{seastrainer_partMESC_ColName, 
																				seastrainer_partMESC_ColSize, 
																				seastrainer_partMESC_ColPrice});
		asm.addOntologyLink(seastrainer_partMESC, uriPartNo);
		asm.addOntologyLink(seastrainer_partMESC_ColName, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/enclosed-cooling-system.omdoc?enclosed-cooling-system?sea-strainer");
		asm.addOntologyLink(seastrainer_partMESC_ColSize, uriSize);
		asm.addOntologyLink(seastrainer_partMESC_ColPrice, uriPrice);
				
		//pipe end
		Integer pipeend_partMESC_ColName = setColTableHeaders(workSheetid, 10, 2, new String[] {"Pipe End-2172", "Pipe End-2172", "Pipe End-2172"});
		Integer pipeend_partMESC_ColSize = setColTableHeaders(workSheetid, 10, 3, new String[] {"S", "M", "XL"});
		Integer pipeend_partMESC_ColPrice = setColTableHeaders(workSheetid, 10, 4, new String[] {"6.40 EUR", "6.50 EUR", "6.60 EUR"});
		Integer pipeend_partMESC = createColFB(workSheetid, 10, 1, new String[] {"1244-2172-1", "1244-2172-2", "1244-2172-4"}, 
																  new Integer[]{pipeend_partMESC_ColName, 
																				pipeend_partMESC_ColSize, 
																				pipeend_partMESC_ColPrice});
		asm.addOntologyLink(pipeend_partMESC, uriPartNo);
		asm.addOntologyLink(pipeend_partMESC_ColName, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/piping.omdoc?piping?clean-out");
		asm.addOntologyLink(pipeend_partMESC_ColSize, uriSize);
		asm.addOntologyLink(pipeend_partMESC_ColPrice, uriPrice);	
			
		//hose
		Integer hose_partMESC_ColName = setColTableHeaders(workSheetid, 13, 2, new String[] {"Hose-2256", "Hose-2256", "Hose-2256"});
		Integer hose_partMESC_ColSize = setColTableHeaders(workSheetid, 13, 3, new String[] {"S", "M", "XL"});
		Integer hose_partMESC_ColPrice = setColTableHeaders(workSheetid, 13, 4, new String[] {"20.88 EUR", "24.88 EUR", "28.88 EUR"});
		Integer hose_partMESC = createColFB(workSheetid, 13, 1, new String[] {"1244-2256-1", "1244-2256-2", "1244-2256-4"}, 
																  new Integer[]{hose_partMESC_ColName, 
																				hose_partMESC_ColSize, 
																				hose_partMESC_ColPrice});
		asm.addOntologyLink(hose_partMESC, uriPartNo);
		asm.addOntologyLink(hose_partMESC_ColName, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/piping.omdoc?piping?pipe");
		asm.addOntologyLink(hose_partMESC_ColSize, uriSize);
		asm.addOntologyLink(hose_partMESC_ColPrice, uriPrice);			
		
		//Water Pump
		Integer waterpump_partMESC_ColName = setColTableHeaders(workSheetid, 16, 2, new String[] {"Water Pump-2198", "Water Pump-2198", "Water Pump-2198"});
		Integer waterpump_partMESC_ColSize = setColTableHeaders(workSheetid, 16, 3, new String[] {"S", "M", "L"});
		Integer waterpump_partMESC_ColPrice = setColTableHeaders(workSheetid, 16, 4, new String[] {"1,099.00 EUR", "2,299.00 EUR", "3,450.00 EUR"});
		Integer waterpump_partMESC = createColFB(workSheetid, 16, 1, new String[] {"1244-2198-1", "1244-2198-2", "1244-2198-3"}, 
																  new Integer[]{waterpump_partMESC_ColName, 
																				waterpump_partMESC_ColSize, 
																				waterpump_partMESC_ColPrice});
		asm.addOntologyLink(waterpump_partMESC, uriPartNo);
		asm.addOntologyLink(waterpump_partMESC_ColName, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/enclosed-cooling-system.omdoc?enclosed-cooling-system?water-pump");
		asm.addOntologyLink(waterpump_partMESC_ColSize, uriSize);
		asm.addOntologyLink(waterpump_partMESC_ColPrice, uriPrice);			
		
		//Quantity
		//Integer partMESC = setColTableHeaders(workSheetid, 3, 1, new String[] {"1244-2211-1", "1244-2211-2", "1244-2211-4", "1244-2207-1", "1244-2207-3", "1244-2207-4", "1244-2172-1", "1244-2172-2", "1244-2172-2", "1244-2256-1", "1244-2256-2", "1244-2256-4", "1244-2198-1", "1244-2198-2", "1244-2198-3"}); 
		//Integer partMESC_ColQuantity = createColFB(workSheetid, 3, 5, new String[] {"40", "20", "2", "40", "10", "4", "960", "720", "400", "480", "360", "200", "20", "10", "2"},
		//															  new Integer[]{partMESC});
		//asm.addOntologyLink(partMESC_ColQuantity, uriQuantity);
		//Integer partMESC_ColVolumePrice = setColTableHeaders(workSheetid, 3, 6, new String[] {"7,540.00 EUR", "6,570.00 EUR", "1,295.00 EUR", "4,800.00 EUR", "1,300.00 EUR", "560.00 EUR", "6,144.00 EUR", "4,680.00 EUR", "2,640.00 EUR", "10,022.40 EUR", "8,956.80 EUR", "5,776.00 EUR", "21,980.00 EUR", "22,990.00 EUR", "6,900.00 EUR"});
		//Part No uses Name, Size, Quantity and Price
		//		new Integer[]{partMESC_ColQuantity, partMESC_ColVolumePrice});

		//asm.addOntologyLink(tableProps, "https://tnt.kwarc.info/repos/stc/fcad/flange/cds/component.omdoc?component?ids");
		//asm.addOntologyLink(partMESC, uriPartNo);
	}
	

	public void writeRDF() {
		OutputStream file;
		try {
			file = new FileOutputStream("iui-model.rdf");
			asm.getRDFModel().write(file);
			Model model = asm.getRDFModel();
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void writeProto() {
		OutputStream file;
		try {
			file = new FileOutputStream("iui-model.rdf.64");
			ByteArrayOutputStream so = new ByteArrayOutputStream();
			SpreadsheetModel model = getAsm().serialize();
			model.writeTo(so);
			byte[] b = Base64.encodeBase64(so.toByteArray());
			file.write(b);
			file.write(new byte[]{10, 10});

			int off = 0; int len = b.length;
			while (len>0) {
				int toWrite = Math.min(10000, len);
				file.write(b, off, toWrite);
				file.write(new byte[]{10});
				len -= toWrite;
				off += toWrite;
			}

			file.close();

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public ASMInterface getAsm() {
		return asm;
	}
	
	public Model getModel() {
		return asm.getRDFModel();
	}
	
	public static void main(String[] args) {
		IUIPaperData t = new IUIPaperData();
		
		t.setData();
		t.writeRDF();
		t.writeProto();
		
	}
}
